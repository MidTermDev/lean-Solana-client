//! The reference for tests/anchor.lean, tests/transaction.lean and tests/versions.lean.
//!
//! Runs the same instructions and transactions, on the same accounts at the
//! same addresses, on Agave's program runtime (through LiteSVM), and prints
//! the same report. `make oracle` builds this, runs it, and compares its
//! output with tests/expected/anchor.txt and tests/expected/transaction.txt,
//! which the Lean virtual machine must reproduce: results, fees, compute
//! units, logs and account contents.
//!
//! This file is built twice: by tests/oracle against Agave 3.1 and by
//! tests/oracle-next against Agave 4.3, which also runs sBPF v3 and, with
//! the BLS library the validators use, prints the report of tests/bls.lean.
//!
//!     oracle anchor anchor_vault.so anchor_vault_v3.so
//!     oracle transaction sysvar_probe.so counter.so
//!     oracle versions sysvar_probe_v1.so sysvar_probe_v2.so ...
//!     oracle-next bls
//!
//! Set ORACLE_RAW=1 to also print Agave's complete log, which shows how many
//! compute units each program consumed at each level of a call.

use {
    litesvm::LiteSVM,
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_address::{address, Address},
    solana_instruction::{account_meta::AccountMeta, error::InstructionError, Instruction},
    solana_keypair::Keypair,
    solana_message::{v0, AddressLookupTableAccount, Message, VersionedMessage},
    solana_signer::Signer,
    solana_transaction::{versioned::VersionedTransaction, Transaction, TransactionError},
};

const TOKEN: Address = address!("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");
const ASSOCIATED_TOKEN: Address = address!("ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL");
const SYSTEM: Address = address!("11111111111111111111111111111111");
const VAULT_PROGRAM: Address = address!("7Ygt9ghxooFNu4aH8TbsNpvXVTZUxQx45Dm6dvYQHKYJ");

fn hash(name: &str) -> [u8; 32] {
    Sha256::digest(name.as_bytes()).into()
}

/// Anchor names an instruction by the first 8 bytes of sha256("global:<name>").
fn instruction_data(name: &str, amount: Option<u64>) -> Vec<u8> {
    let mut data = hash(&format!("global:{name}"))[..8].to_vec();
    if let Some(amount) = amount {
        data.extend_from_slice(&amount.to_le_bytes());
    }
    data
}

fn token_balance(svm: &LiteSVM, account: &Address) -> u64 {
    u64::from_le_bytes(svm.get_account(account).unwrap().data[64..72].try_into().unwrap())
}

/// Sends one instruction and prints how it went, the way tests/anchor.lean does.
fn run(svm: &mut LiteSVM, label: &str, payer: &Keypair, signers: &[&Keypair], ix: Instruction) {
    let message = Message::new(&[ix], Some(&payer.pubkey()));
    let tx = Transaction::new(signers, message, svm.latest_blockhash());
    let (outcome, units, logs) = match svm.send_transaction(tx) {
        Ok(meta) => ("success".to_string(), meta.compute_units_consumed, meta.logs),
        Err(failed) => {
            let why = match failed.err {
                TransactionError::InstructionError(_, InstructionError::Custom(code)) => format!("custom error {code}"),
                TransactionError::InstructionError(_, other) => format!("{other:?}"),
                other => format!("{other:?}"),
            };
            (why, failed.meta.compute_units_consumed, failed.meta.logs)
        }
    };
    println!("{label}: {outcome}, {units} units");
    for line in logs {
        if std::env::var_os("ORACLE_RAW").is_some() {
            println!("  raw: {line}");
        }
        if let Some(text) = line.strip_prefix("Program log: ") {
            println!("  log: {text}");
        } else if let Some(data) = line.strip_prefix("Program data: ") {
            println!("  log: data: {data}");
        }
    }
    svm.expire_blockhash();
}

fn anchor(program: &str) {
    let bytes = std::fs::read(program).unwrap();
    if bytes[48] != 0 {
        println!("the same program compiled for sBPF v{}:", bytes[48]);
    }
    let mut svm = LiteSVM::new();
    svm.add_program(VAULT_PROGRAM, &std::fs::read(program).unwrap()).unwrap();

    let owner = Keypair::new_from_array(hash("owner"));
    let stranger = Keypair::new_from_array(hash("stranger"));
    svm.airdrop(&owner.pubkey(), 10_000_000_000).unwrap();
    svm.airdrop(&stranger.pubkey(), 10_000_000_000).unwrap();

    // a mint with 6 decimals and 5,000,000 units in existence, all held by the owner
    let mint = Address::new_from_array(hash("mint"));
    let mut data = vec![1, 0, 0, 0];
    data.extend_from_slice(owner.pubkey().as_ref());
    data.extend_from_slice(&5_000_000u64.to_le_bytes());
    data.extend_from_slice(&[6, 1]);
    data.resize(82, 0);
    svm.set_account(mint, Account { lamports: 10_000_000, data, owner: TOKEN, ..Default::default() }).unwrap();

    let owner_tokens = Address::new_from_array(hash("owner tokens"));
    let mut data = mint.as_ref().to_vec();
    data.extend_from_slice(owner.pubkey().as_ref());
    data.extend_from_slice(&5_000_000u64.to_le_bytes());
    data.resize(108, 0);
    data.push(1);
    data.resize(165, 0);
    svm.set_account(owner_tokens, Account { lamports: 10_000_000, data, owner: TOKEN, ..Default::default() }).unwrap();

    let (vault, bump) = Address::find_program_address(&[b"vault", mint.as_ref(), owner.pubkey().as_ref()], &VAULT_PROGRAM);
    let (vault_tokens, _) = Address::find_program_address(&[vault.as_ref(), TOKEN.as_ref(), mint.as_ref()], &ASSOCIATED_TOKEN);
    println!("owner {}", owner.pubkey());
    println!("vault {vault} (bump {bump})");
    println!("vault tokens {vault_tokens}");

    // 1. initialize: the vault's state account and its token account come into being
    let initialize = Instruction {
        program_id: VAULT_PROGRAM,
        accounts: vec![
            AccountMeta::new(owner.pubkey(), true),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault, false),
            AccountMeta::new(vault_tokens, false),
            AccountMeta::new_readonly(TOKEN, false),
            AccountMeta::new_readonly(ASSOCIATED_TOKEN, false),
            AccountMeta::new_readonly(SYSTEM, false),
        ],
        data: instruction_data("initialize", None),
    };
    run(&mut svm, "initialize", &owner, &[&owner], initialize.clone());
    let state = svm.get_account(&vault).unwrap();
    println!("  vault: {} bytes, {} lamports, owned by the vault program: {}", state.data.len(), state.lamports, state.owner == VAULT_PROGRAM);
    let tokens = svm.get_account(&vault_tokens).unwrap();
    println!("  vault tokens: {} bytes, {} lamports, owned by the token program: {}", tokens.data.len(), tokens.lamports, tokens.owner == TOKEN);
    // a second time must fail: the accounts already exist
    run(&mut svm, "initialize again", &owner, &[&owner], initialize);

    let transfer = |name: &str, amount: u64, signer: &Keypair| Instruction {
        program_id: VAULT_PROGRAM,
        accounts: vec![
            AccountMeta::new_readonly(signer.pubkey(), true),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault, false),
            AccountMeta::new(vault_tokens, false),
            AccountMeta::new(owner_tokens, false),
            AccountMeta::new_readonly(TOKEN, false),
        ],
        data: instruction_data(name, Some(amount)),
    };
    let report = |svm: &LiteSVM| {
        let recorded = u64::from_le_bytes(svm.get_account(&vault).unwrap().data[72..80].try_into().unwrap());
        println!("  vault holds {}, owner holds {}, recorded {recorded}", token_balance(svm, &vault_tokens), token_balance(svm, &owner_tokens));
    };

    // 2. deposit: the owner signs the token transfer
    run(&mut svm, "deposit 1500000", &owner, &[&owner], transfer("deposit", 1_500_000, &owner));
    report(&svm);
    // 3. withdraw: the vault signs, with the seeds of its address
    run(&mut svm, "withdraw 400000", &owner, &[&owner], transfer("withdraw", 400_000, &owner));
    report(&svm);
    // 4. more than the vault holds: the program refuses
    run(&mut svm, "withdraw 2000000", &owner, &[&owner], transfer("withdraw", 2_000_000, &owner));
    report(&svm);
    // 5. somebody else: Anchor's account checks refuse
    run(&mut svm, "withdraw by a stranger", &stranger, &[&stranger], transfer("withdraw", 1, &stranger));
    report(&svm);
}

// ------------------------------------------------------------ transactions

const COMPUTE_BUDGET: Address = address!("ComputeBudget111111111111111111111111111111");
const ED25519: Address = address!("Ed25519SigVerify111111111111111111111111111");

fn budget(tag: u8, value: u64, width: usize) -> Instruction {
    let mut data = vec![tag];
    data.extend_from_slice(&value.to_le_bytes()[..width]);
    Instruction { program_id: COMPUTE_BUDGET, accounts: vec![], data }
}
fn unit_limit(units: u32) -> Instruction { budget(2, units as u64, 4) }
fn unit_price(micro_lamports: u64) -> Instruction { budget(3, micro_lamports, 8) }
fn heap_frame(bytes: u32) -> Instruction { budget(1, bytes as u64, 4) }

fn transfer(from: &Address, to: &Address, lamports: u64) -> Instruction {
    let mut data = 2u32.to_le_bytes().to_vec();
    data.extend_from_slice(&lamports.to_le_bytes());
    Instruction { program_id: SYSTEM, accounts: vec![AccountMeta::new(*from, true), AccountMeta::new(*to, false)], data }
}

fn create_account(from: &Address, new: &Address, lamports: u64, space: u64, owner: &Address) -> Instruction {
    let mut data = 0u32.to_le_bytes().to_vec();
    data.extend_from_slice(&lamports.to_le_bytes());
    data.extend_from_slice(&space.to_le_bytes());
    data.extend_from_slice(owner.as_ref());
    Instruction { program_id: SYSTEM, accounts: vec![AccountMeta::new(*from, true), AccountMeta::new(*new, true)], data }
}

/// An instruction for the Ed25519 program: check `signer`'s signature of `message`.
/// `claimed` is the message the instruction says was signed.
fn ed25519(signer: &Keypair, message: &[u8], claimed: &[u8]) -> Instruction {
    let mut data = vec![1u8, 0];
    for field in [48u16, u16::MAX, 16, u16::MAX, 112, claimed.len() as u16, u16::MAX] {
        data.extend_from_slice(&field.to_le_bytes());
    }
    data.extend_from_slice(signer.pubkey().as_ref());
    data.extend_from_slice(signer.sign_message(message).as_ref());
    data.extend_from_slice(claimed);
    Instruction { program_id: ED25519, accounts: vec![], data }
}

struct Chain {
    svm: LiteSVM,
    payer: Keypair,
    alice: Keypair,
}

impl Chain {
    /// Sends a transaction and prints what happened, the way tests/transaction.lean does.
    fn send(&mut self, label: &str, tx: impl Into<VersionedTransaction>) {
        let tx: VersionedTransaction = tx.into();
        let signature = tx.signatures[0];
        let (outcome, fee, units, logs) = match self.svm.send_transaction(tx) {
            Ok(meta) => ("success".to_string(), meta.fee, meta.compute_units_consumed, meta.logs),
            Err(failed) => (format!("{:?}", failed.err), failed.meta.fee, failed.meta.compute_units_consumed, failed.meta.logs),
        };
        println!("{label}: {outcome}, fee {fee}, {units} units");
        println!("  signature {signature}");
        for line in logs {
            if std::env::var_os("ORACLE_RAW").is_some() {
                println!("  raw: {line}");
            }
            if let Some(text) = line.strip_prefix("Program log: ") {
                println!("  log: {text}");
            } else if let Some(data) = line.strip_prefix("Program data: ") {
                println!("  log: data: {data}");
            }
        }
        println!("  payer {}, alice {}", self.balance(&self.payer.pubkey()), self.balance(&self.alice.pubkey()));
    }

    fn balance(&self, address: &Address) -> u64 {
        self.svm.get_balance(address).unwrap_or(0)
    }

    fn build(&self, payer: &Keypair, signers: &[&Keypair], instructions: &[Instruction]) -> Transaction {
        Transaction::new(signers, Message::new(instructions, Some(&payer.pubkey())), self.svm.latest_blockhash())
    }

    /// A transaction paid for and signed by the usual payer alone.
    fn run(&mut self, label: &str, instructions: &[Instruction]) {
        let tx = self.build(&self.payer, &[&self.payer], instructions);
        self.send(label, tx);
    }
}

fn transaction(probe_so: &str, counter_so: &str) {
    let probe = Address::new_from_array(hash("sysvar probe"));
    let counter = Address::new_from_array(hash("counter program"));
    let mut svm = LiteSVM::new().with_precompiles();
    svm.add_program(probe, &std::fs::read(probe_so).unwrap()).unwrap();
    svm.add_program(counter, &std::fs::read(counter_so).unwrap()).unwrap();
    let wallet = |lamports| Account { lamports, owner: SYSTEM, ..Default::default() };
    let payer = Keypair::new_from_array(hash("payer"));
    let alice = Keypair::new_from_array(hash("alice"));
    let bob = Keypair::new_from_array(hash("bob"));
    let poor = Keypair::new_from_array(hash("poor"));
    let nobody = Keypair::new_from_array(hash("nobody"));
    svm.set_account(payer.pubkey(), wallet(10_000_000_000)).unwrap();
    svm.set_account(alice.pubkey(), wallet(2_000_000_000)).unwrap();
    svm.set_account(poor.pubkey(), wallet(3_000)).unwrap();
    println!("blockhash {}", svm.latest_blockhash());
    let mut chain = Chain { svm, payer, alice };
    let payer = chain.payer.pubkey();
    let alice = chain.alice.pubkey();
    let probe_ix = |mode: u8, accounts: Vec<AccountMeta>| Instruction { program_id: probe, accounts, data: vec![mode] };
    let counter_ix = |data: Vec<u8>| Instruction { program_id: counter, accounts: vec![AccountMeta::new(bob.pubkey(), false)], data };
    let sysvar = |name: &str| AccountMeta::new_readonly(name.parse::<Address>().unwrap(), false);
    let instructions_sysvar = "Sysvar1nstructions1111111111111111111111111";

    // fees: 5,000 lamports per signature, plus the price offered per compute unit of the limit
    chain.run("transfer, with a priority fee", &[unit_limit(300_000), unit_price(2_500), transfer(&payer, &alice, 1_000_000_000)]);

    // the sysvars, as a program sees them
    chain.run("sysvars by system call", &[probe_ix(0, vec![])]);
    chain.run("sysvars by address", &[probe_ix(3, vec![])]);
    chain.run("sysvar accounts", &[unit_limit(1_400_000), probe_ix(1, vec![
        sysvar("SysvarC1ock11111111111111111111111111111111"),
        sysvar("SysvarEpochSchedu1e111111111111111111111111"),
        sysvar("SysvarEpochRewards1111111111111111111111111"),
        sysvar("SysvarFees111111111111111111111111111111111"),
        sysvar("SysvarLastRestartS1ot1111111111111111111111"),
        sysvar("SysvarRecentB1ockHashes11111111111111111111"),
        sysvar("SysvarRent111111111111111111111111111111111"),
        sysvar("SysvarS1otHashes111111111111111111111111111"),
        sysvar("SysvarS1otHistory11111111111111111111111111"),
        sysvar("SysvarStakeHistory1111111111111111111111111"),
        sysvar(instructions_sysvar),
    ])]);
    chain.run("a program reads its own transaction", &[unit_price(1), transfer(&payer, &alice, 5_000),
        probe_ix(2, vec![sysvar(instructions_sysvar)])]);

    // several instructions, two signers: create an account, hand it to the counter program, count twice
    let count = |chain: &Chain| match chain.svm.get_account(&bob.pubkey()) {
        Some(account) => println!("  count {}", u64::from_le_bytes(account.data[..8].try_into().unwrap())),
        None => println!("  the counter account does not exist"),
    };
    let tx = chain.build(&chain.payer, &[&chain.payer, &bob], &[create_account(&payer, &bob.pubkey(), 946_560, 8, &counter),
        counter_ix(vec![0]), counter_ix(vec![1]), counter_ix(vec![1])]);
    chain.send("create an account and count twice", tx);
    count(&chain);

    // all or nothing: the third instruction overflows, so the transfer and the first count are undone. The fee is not.
    let mut overflow = vec![2u8];
    overflow.extend_from_slice(&u64::MAX.to_le_bytes());
    chain.run("the last instruction fails", &[transfer(&payer, &alice, 7), counter_ix(vec![1]), counter_ix(overflow)]);
    count(&chain);

    // rent: an account may not be left with a balance too small to keep it alive
    chain.run("leaves an account below the rent minimum", &[transfer(&payer, &Address::new_from_array(hash("pauper")), 1_000)]);

    // the Ed25519 program: signatures checked by the runtime, visible to programs through the Instructions sysvar
    let signed = ed25519(&chain.alice, b"hello", b"hello");
    chain.run("a signature checked by the runtime", &[signed, probe_ix(2, vec![sysvar(instructions_sysvar)])]);
    let forged = ed25519(&chain.alice, b"hello", b"jello");
    chain.run("a signature that does not match", &[forged, transfer(&payer, &alice, 9)]);

    // the compute budget
    chain.run("the same budget instruction twice", &[unit_limit(1_000), unit_limit(2_000), transfer(&payer, &alice, 11)]);
    chain.run("a heap size that is not allowed", &[heap_frame(1_000), probe_ix(0, vec![])]);
    chain.run("a bigger heap costs units", &[heap_frame(65_536), probe_ix(0, vec![])]);
    chain.run("a budget the program exceeds", &[unit_limit(2_000), probe_ix(0, vec![])]);
    chain.run("a budget too small for a transfer", &[unit_limit(200), transfer(&payer, &alice, 13)]);
    chain.run("a budget of nothing", &[unit_limit(0), transfer(&payer, &alice, 15)]);

    // who pays
    let tx = chain.build(&nobody, &[&nobody], &[transfer(&nobody.pubkey(), &alice, 1)]);
    chain.send("a payer that does not exist", tx);
    let tx = chain.build(&poor, &[&poor], &[transfer(&poor.pubkey(), &alice, 1)]);
    chain.send("a payer that cannot afford the fee", tx);
    let mut tx = chain.build(&chain.payer, &[&chain.payer], &[transfer(&payer, &alice, 17)]);
    let mut bytes: [u8; 64] = tx.signatures[0].into();
    bytes[0] ^= 1;
    tx.signatures[0] = bytes.into();
    chain.send("a signature that was tampered with", tx);

    // an account emptied by a transaction ceases to exist
    let all = chain.balance(&alice);
    let tx = chain.build(&chain.payer, &[&chain.payer, &chain.alice], &[transfer(&alice, &payer, all)]);
    chain.send("alice sends everything she has", tx);
    println!("  alice exists: {}", chain.svm.get_account(&alice).is_some());
}

/// The same program compiled for several versions of sBPF: each must load and
/// behave the same, at its own cost in compute units.
fn versions(files: &[String]) {
    let mut svm = LiteSVM::new();
    let wallet = |lamports| Account { lamports, owner: SYSTEM, ..Default::default() };
    let payer = Keypair::new_from_array(hash("payer"));
    let alice = Keypair::new_from_array(hash("alice"));
    svm.set_account(payer.pubkey(), wallet(10_000_000_000)).unwrap();
    svm.set_account(alice.pubkey(), wallet(2_000_000_000)).unwrap();
    println!("blockhash {}", svm.latest_blockhash());
    let mut loaded = vec![];
    for file in files {
        let bytes = std::fs::read(file).unwrap();
        let version = bytes[48];
        let program = Address::new_from_array(hash(&format!("probe for sBPF v{version}")));
        match svm.add_program(program, &bytes) {
            Ok(_) => loaded.push((version, program)),
            Err(_) => println!("sBPF v{version}: this runtime does not accept the program"),
        }
    }
    let mut chain = Chain { svm, payer, alice };
    let payer = chain.payer.pubkey();
    let alice = chain.alice.pubkey();
    for (version, program) in loaded {
        let mut numbers = vec![4u8];
        for n in [0xFEDC_BA98_7654_3210u64, 0x0123_4567_89AB_CDEF, 1_000_003] {
            numbers.extend_from_slice(&n.to_le_bytes());
        }
        chain.run(&format!("sBPF v{version}, arithmetic"), &[Instruction { program_id: program, accounts: vec![], data: numbers }]);
        let sysvar = AccountMeta::new_readonly("Sysvar1nstructions1111111111111111111111111".parse::<Address>().unwrap(), false);
        chain.run(&format!("sBPF v{version}, reads its own transaction"), &[transfer(&payer, &alice, 1_000 + version as u64),
            Instruction { program_id: program, accounts: vec![sysvar], data: vec![2] }]);
    }
}

// ------------------------------------------------------- built-in programs

const CONFIG: Address = address!("Config1111111111111111111111111111111111111");
const LOOKUP_TABLE: Address = address!("AddressLookupTab1e1111111111111111111111111");
const STAKE: Address = address!("Stake11111111111111111111111111111111111111");
const RECENT_BLOCKHASHES: Address = address!("SysvarRecentB1ockHashes11111111111111111111");
const RENT: Address = address!("SysvarRent111111111111111111111111111111111");
const CLOCK: Address = address!("SysvarC1ock11111111111111111111111111111111");
const STAKE_HISTORY: Address = address!("SysvarStakeHistory1111111111111111111111111");

/// A system program instruction: a 32-bit tag, then the fields given.
fn system(tag: u32, fields: &[&[u8]], accounts: Vec<AccountMeta>) -> Instruction {
    Instruction { program_id: SYSTEM, accounts, data: [&tag.to_le_bytes()[..], &fields.concat()].concat() }
}
fn tagged(program_id: Address, tag: u32, fields: &[&[u8]], accounts: Vec<AccountMeta>) -> Instruction {
    Instruction { program_id, accounts, data: [&tag.to_le_bytes()[..], &fields.concat()].concat() }
}
fn text(s: &str) -> Vec<u8> {
    [&(s.len() as u64).to_le_bytes()[..], s.as_bytes()].concat()
}
fn with_seed(base: &Address, seed: &str, owner: &Address) -> Address {
    Address::new_from_array(Sha256::digest([base.as_ref(), seed.as_bytes(), owner.as_ref()].concat()).into())
}
fn w(key: Address) -> AccountMeta { AccountMeta::new(key, false) }
fn ws(key: Address) -> AccountMeta { AccountMeta::new(key, true) }
fn r(key: Address) -> AccountMeta { AccountMeta::new_readonly(key, false) }
fn rs(key: Address) -> AccountMeta { AccountMeta::new_readonly(key, true) }

impl Chain {
    /// One line describing an account: balance, size, owner and a hash of its data.
    fn show(&self, name: &str, key: &Address) {
        match self.svm.get_account(key) {
            Some(a) => println!("  {name}: {} lamports, {} bytes, owner {}, data {}", a.lamports, a.data.len(), a.owner,
                Address::new_from_array(Sha256::digest(&a.data).into())),
            None => println!("  {name}: no such account"),
        }
    }
    fn signed(&mut self, label: &str, extra: &[&Keypair], instructions: &[Instruction]) {
        let mut signers = vec![&self.payer];
        signers.extend_from_slice(extra);
        let tx = Transaction::new(&signers, Message::new(instructions, Some(&self.payer.pubkey())), self.svm.latest_blockhash());
        self.send(label, tx);
    }
}

const LOADER: Address = address!("BPFLoaderUpgradeab1e11111111111111111111111");

/// Uploads `code` into a new buffer account, 900 bytes per transaction.
fn upload(chain: &mut Chain, name: &str, code: &[u8]) -> Address {
    let buffer_keys = Keypair::new_from_array(hash(name));
    let buffer = buffer_keys.pubkey();
    let payer = chain.payer.pubkey();
    let size = 37 + code.len();
    let rent = (128 + size as u64) * 6960;
    chain.signed(&format!("create {name}"), &[&buffer_keys], &[create_account(&payer, &buffer, rent, size as u64, &LOADER),
        tagged(LOADER, 0, &[], vec![w(buffer), r(payer)])]);
    for (i, chunk) in code.chunks(900).enumerate() {
        chain.signed(&format!("write piece {i} into {name}"), &[], &[tagged(LOADER, 1,
            &[&((i * 900) as u32).to_le_bytes(), &(chunk.len() as u64).to_le_bytes(), chunk], vec![w(buffer), rs(payer)])]);
    }
    chain.show(name, &buffer);
    buffer
}

fn builtins(counter_so: &str, noop_so: &str) {
    let mut svm = LiteSVM::new();
    let wallet = |lamports| Account { lamports, owner: SYSTEM, ..Default::default() };
    let payer_keys = Keypair::new_from_array(hash("payer"));
    let alice_keys = Keypair::new_from_array(hash("alice"));
    svm.set_account(payer_keys.pubkey(), wallet(10_000_000_000)).unwrap();
    svm.set_account(alice_keys.pubkey(), wallet(2_000_000_000)).unwrap();
    println!("blockhash {}", svm.latest_blockhash());
    let mut chain = Chain { svm, payer: payer_keys, alice: alice_keys };
    let payer = chain.payer.pubkey();
    let alice = chain.alice.pubkey();
    let alice_keys = Keypair::new_from_array(hash("alice"));

    // --- the system program: addresses derived from a base key and a seed
    let vault = with_seed(&payer, "vault", &SYSTEM);
    chain.signed("create an account at a seed-derived address", &[], &[system(3, &[payer.as_ref(), &text("vault"),
        &1_000_000_000u64.to_le_bytes(), &0u64.to_le_bytes(), SYSTEM.as_ref()], vec![ws(payer), w(vault)])]);
    chain.show("vault", &vault);
    chain.signed("transfer out of it, signed by the base", &[], &[system(11, &[&250_000_000u64.to_le_bytes(), &text("vault"),
        SYSTEM.as_ref()], vec![w(vault), rs(payer), w(alice)])]);
    chain.show("vault", &vault);
    chain.signed("transfer with the wrong seed", &[], &[system(11, &[&1u64.to_le_bytes(), &text("vaults"),
        SYSTEM.as_ref()], vec![w(vault), rs(payer), w(alice)])]);
    let ledger = with_seed(&payer, "ledger", &CONFIG);
    chain.signed("fund, allocate and assign a seed-derived address", &[], &[transfer(&payer, &ledger, 1_447_680),
        system(9, &[payer.as_ref(), &text("ledger"), &80u64.to_le_bytes(), CONFIG.as_ref()], vec![w(ledger), rs(payer)]),
        system(10, &[payer.as_ref(), &text("ledger"), CONFIG.as_ref()], vec![w(ledger), rs(payer)])]);
    chain.show("ledger", &ledger);
    chain.signed("a seed longer than 32 bytes", &[], &[system(9, &[payer.as_ref(), &text("a seed that is much longer than is allowed"),
        &80u64.to_le_bytes(), CONFIG.as_ref()], vec![w(ledger), rs(payer)])]);

    // --- the system program: nonce accounts
    let nonce_keys = Keypair::new_from_array(hash("nonce"));
    let nonce = nonce_keys.pubkey();
    chain.signed("create a nonce account", &[&nonce_keys], &[create_account(&payer, &nonce, 2_000_000, 80, &SYSTEM),
        system(6, &[payer.as_ref()], vec![w(nonce), r(RECENT_BLOCKHASHES), r(RENT)])]);
    chain.show("nonce", &nonce);
    chain.signed("initialize it again", &[], &[system(6, &[alice.as_ref()], vec![w(nonce), r(RECENT_BLOCKHASHES), r(RENT)])]);
    chain.signed("advance it before the blockhash changed", &[], &[system(4, &[], vec![w(nonce), r(RECENT_BLOCKHASHES), rs(payer)])]);
    chain.signed("give it to alice", &[], &[system(7, &[alice.as_ref()], vec![w(nonce), rs(payer)])]);
    chain.show("nonce", &nonce);
    chain.signed("the old authority tries to advance it", &[], &[transfer(&payer, &alice, 1),
        system(4, &[], vec![w(nonce), r(RECENT_BLOCKHASHES), rs(payer)])]);
    chain.signed("alice withdraws a little", &[&alice_keys], &[system(5, &[&100_000u64.to_le_bytes()],
        vec![w(nonce), w(alice), r(RECENT_BLOCKHASHES), r(RENT), rs(alice)])]);
    chain.signed("alice withdraws too much", &[&alice_keys], &[system(5, &[&500_000u64.to_le_bytes()],
        vec![w(nonce), w(alice), r(RECENT_BLOCKHASHES), r(RENT), rs(alice)])]);
    chain.svm.expire_blockhash();
    println!("blockhash {}", chain.svm.latest_blockhash());
    chain.signed("advance it after the blockhash changed", &[&alice_keys], &[system(4, &[], vec![w(nonce), r(RECENT_BLOCKHASHES), rs(alice)])]);
    chain.show("nonce", &nonce);
    chain.signed("advance it twice", &[&alice_keys], &[transfer(&payer, &alice, 2), system(4, &[], vec![w(nonce), r(RECENT_BLOCKHASHES), rs(alice)])]);
    chain.signed("close it while its nonce is current", &[&alice_keys], &[system(5, &[&1_900_000u64.to_le_bytes()],
        vec![w(nonce), w(alice), r(RECENT_BLOCKHASHES), r(RENT), rs(alice)])]);
    chain.show("nonce", &nonce);

    // --- the config program (bytecode): a record with a list of keys that must sign changes to it
    let record_keys = Keypair::new_from_array(hash("record"));
    let record = record_keys.pubkey();
    let mut store = vec![1u8];
    store.extend_from_slice(alice.as_ref());
    store.push(1);
    store.extend_from_slice(b"what the record says");
    chain.signed("create a config record", &[&record_keys, &alice_keys], &[create_account(&payer, &record, 1_670_400, 112, &CONFIG),
        Instruction { program_id: CONFIG, accounts: vec![ws(record), rs(alice)], data: store.clone() }]);
    chain.show("record", &record);
    store[40] = b'W';
    chain.signed("change it without the key it names", &[&record_keys], &[Instruction { program_id: CONFIG, accounts: vec![ws(record)], data: store.clone() }]);
    chain.signed("change it with that key", &[&alice_keys], &[Instruction { program_id: CONFIG, accounts: vec![w(record), rs(alice)], data: store }]);
    chain.show("record", &record);

    // --- address lookup tables (bytecode): create one, add addresses, then use it in a version 0 transaction
    let (table, bump) = Address::find_program_address(&[payer.as_ref(), &0u64.to_le_bytes()], &LOOKUP_TABLE);
    let carol = Address::new_from_array(hash("carol"));
    let dave = Address::new_from_array(hash("dave"));
    chain.signed("create a lookup table", &[], &[tagged(LOOKUP_TABLE, 0, &[&0u64.to_le_bytes(), &[bump]],
        vec![w(table), r(payer), ws(payer), r(SYSTEM)])]);
    chain.show("table", &table);
    chain.signed("add two addresses to it", &[], &[tagged(LOOKUP_TABLE, 2, &[&2u64.to_le_bytes(), carol.as_ref(), dave.as_ref()],
        vec![w(table), rs(payer), ws(payer), r(SYSTEM)])]);
    chain.show("table", &table);
    let lookup = AddressLookupTableAccount { key: table, addresses: vec![carol, dave] };
    let via_table = |chain: &Chain, to: &Address, lamports: u64| {
        let message = v0::Message::try_compile(&payer, &[transfer(&payer, to, lamports)], &[lookup.clone()], chain.svm.latest_blockhash()).unwrap();
        VersionedTransaction::try_new(VersionedMessage::V0(message), &[&chain.payer]).unwrap()
    };
    let tx = via_table(&chain, &dave, 1_000_000_000);
    chain.send("pay an address through the table in the slot it was added", tx);
    chain.svm.warp_to_slot(1);
    let tx = via_table(&chain, &dave, 1_000_000_001);
    chain.send("pay it through the table one slot later", tx);
    chain.show("dave", &dave);
    chain.signed("freeze the table", &[], &[tagged(LOOKUP_TABLE, 1, &[], vec![w(table), rs(payer)])]);
    chain.signed("add to the frozen table", &[], &[tagged(LOOKUP_TABLE, 2, &[&1u64.to_le_bytes(), alice.as_ref()],
        vec![w(table), rs(payer), ws(payer), r(SYSTEM)])]);
    chain.show("table", &table);

    // --- the stake program (bytecode): a stake account is created, handed over, split and drawn down
    let stake_keys = Keypair::new_from_array(hash("stake"));
    let stake = stake_keys.pubkey();
    let half_keys = Keypair::new_from_array(hash("half"));
    let half = half_keys.pubkey();
    chain.signed("create a stake account", &[&stake_keys], &[create_account(&payer, &stake, 3_000_000_000, 200, &STAKE),
        tagged(STAKE, 0, &[payer.as_ref(), payer.as_ref(), &[0u8; 48]], vec![w(stake), r(RENT)])]);
    chain.show("stake", &stake);
    chain.signed("initialize it again", &[], &[tagged(STAKE, 0, &[alice.as_ref(), alice.as_ref(), &[0u8; 48]], vec![w(stake), r(RENT)])]);
    chain.signed("make alice the withdrawer", &[], &[tagged(STAKE, 1, &[alice.as_ref(), &1u32.to_le_bytes()], vec![w(stake), r(CLOCK), rs(payer)])]);
    chain.show("stake", &stake);
    chain.signed("split off a third", &[&half_keys], &[create_account(&payer, &half, 2_282_880, 200, &STAKE),
        tagged(STAKE, 3, &[&1_000_000_000u64.to_le_bytes()], vec![w(stake), w(half), rs(payer)])]);
    chain.show("stake", &stake);
    chain.show("the split", &half);
    chain.signed("the old withdrawer tries to withdraw", &[], &[tagged(STAKE, 4, &[&500_000_000u64.to_le_bytes()],
        vec![w(stake), w(alice), r(CLOCK), r(STAKE_HISTORY), rs(payer)])]);
    chain.signed("alice withdraws", &[&alice_keys], &[tagged(STAKE, 4, &[&500_000_000u64.to_le_bytes()],
        vec![w(stake), w(alice), r(CLOCK), r(STAKE_HISTORY), rs(alice)])]);
    chain.show("stake", &stake);
    chain.signed("alice withdraws below the reserve", &[&alice_keys], &[tagged(STAKE, 4, &[&1_499_000_000u64.to_le_bytes()],
        vec![w(stake), w(alice), r(CLOCK), r(STAKE_HISTORY), rs(alice)])]);

    // --- the loader: a program is uploaded into a buffer, deployed, called, upgraded, handed over, extended, closed
    let counter_code = std::fs::read(counter_so).unwrap();
    let buffer = upload(&mut chain, "a buffer", &counter_code);
    chain.signed("someone else writes into the buffer", &[&alice_keys], &[tagged(LOADER, 1,
        &[&0u32.to_le_bytes(), &4u64.to_le_bytes(), b"oops"], vec![w(buffer), rs(alice)])]);
    let program_keys = Keypair::new_from_array(hash("deployed program"));
    let program = program_keys.pubkey();
    let (program_data, _) = Address::find_program_address(&[program.as_ref()], &LOADER);
    let room = 2 * counter_code.len() as u64;
    chain.signed("deploy the program", &[&program_keys], &[create_account(&payer, &program, 1_141_440, 36, &LOADER),
        tagged(LOADER, 2, &[&room.to_le_bytes()], vec![ws(payer), w(program_data), w(program), w(buffer), r(RENT), r(CLOCK), r(SYSTEM), rs(payer)])]);
    chain.show("program", &program);
    chain.show("program data", &program_data);
    chain.show("a buffer", &buffer);
    chain.svm.warp_to_slot(2);
    let tally_keys = Keypair::new_from_array(hash("tally"));
    let tally = tally_keys.pubkey();
    let call = |data: Vec<u8>| Instruction { program_id: program, accounts: vec![w(tally)], data };
    chain.signed("call the deployed program", &[&tally_keys], &[create_account(&payer, &tally, 946_560, 8, &program),
        call(vec![0]), call(vec![1]), call(vec![1]), call(vec![1])]);
    chain.show("tally", &tally);
    let noop_code = std::fs::read(noop_so).unwrap();
    let second = upload(&mut chain, "a second buffer", &noop_code);
    let upgrade = |authority: Address, buffer: Address| tagged(LOADER, 3, &[], vec![w(program_data), w(program), w(buffer), w(payer), r(RENT), r(CLOCK), rs(authority)]);
    chain.signed("someone else upgrades the program", &[&alice_keys], &[upgrade(alice, second)]);
    chain.signed("upgrade the program", &[], &[upgrade(payer, second)]);
    chain.show("program data", &program_data);
    chain.svm.warp_to_slot(3);
    chain.signed("call the upgraded program", &[], &[transfer(&payer, &alice, 3), call(vec![1])]);
    chain.show("tally", &tally);
    chain.signed("hand the program to alice", &[], &[tagged(LOADER, 4, &[], vec![w(program_data), rs(payer), r(alice)])]);
    chain.signed("the old authority extends it", &[], &[tagged(LOADER, 9, &[&1_000u32.to_le_bytes()],
        vec![w(program_data), w(program), rs(payer), r(SYSTEM), ws(payer)])]);
    chain.signed("alice extends it", &[&alice_keys], &[tagged(LOADER, 9, &[&1_000u32.to_le_bytes()],
        vec![w(program_data), w(program), rs(alice), r(SYSTEM), ws(payer)])]);
    chain.show("program data", &program_data);
    chain.signed("close the second buffer", &[], &[tagged(LOADER, 5, &[], vec![w(second), w(alice), rs(payer)])]);
    chain.show("a second buffer", &second);
    chain.signed("alice makes the program immutable", &[&alice_keys], &[transfer(&payer, &alice, 4), tagged(LOADER, 4, &[], vec![w(program_data), rs(alice)])]);
    chain.signed("alice extends the immutable program", &[&alice_keys], &[tagged(LOADER, 9, &[&8u32.to_le_bytes()],
        vec![w(program_data), w(program), rs(alice), r(SYSTEM), ws(payer)])]);
    chain.show("program data", &program_data);
    chain.signed("an instruction for the old loader", &[], &[Instruction { program_id: address!("BPFLoader2111111111111111111111111111111111"), accounts: vec![], data: vec![0, 0, 0, 0] }]);
}

/// The report of tests/bls.lean, from blstrs: points, signatures, and when a certificate proves a block final.
#[cfg(feature = "bls")]
mod bls {
    use {
        blstrs::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar},
        group::{prime::PrimeCurveAffine, Curve, Group},
    };

    const DOMAIN: &[u8] = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
    const STRAY: &str = "81f9dfd3ee5e608fb85f55642c3d3bed4a69b88bd8296f97c4f48490502da3719c936021975dd7199150f08428f250040cf2ef94da514517fe35d5f02fca8414a72d7007b0718e145f4a4805b35323086d2b5a06ab56eb1d89567961edbd7091";

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn point(message: &[u8]) -> G2Projective {
        G2Projective::hash_to_curve(message, DOMAIN, &[])
    }

    fn holds(key: &G1Projective, message: &[u8], signature: &G2Projective) -> bool {
        !bool::from(key.is_identity())
            && pairing(&key.to_affine(), &point(message).to_affine()) == pairing(&G1Affine::generator(), &signature.to_affine())
    }

    fn verdict(ok: bool) -> &'static str {
        if ok { "holds" } else { "does not hold" }
    }

    fn vote(kind: u8, slot: u64, block: &[u8], version: u16) -> Vec<u8> {
        [&[kind][..], &slot.to_le_bytes(), block, &version.to_le_bytes()].concat()
    }

    struct Validators {
        secrets: Vec<Scalar>,
        keys: Vec<G1Projective>,
        stakes: Vec<u64>,
    }

    impl Validators {
        /// The signatures of `message` by the validators of these ranks, added up and compressed.
        fn signed_by(&self, ranks: &[usize], message: &[u8]) -> [u8; 96] {
            ranks.iter().map(|&r| point(message) * self.secrets[r]).sum::<G2Projective>().to_affine().to_compressed()
        }

        /// The stake of the validators named, if `signature` is their signatures of `message` added up; otherwise 0.
        fn signed_stake(&self, ranks: &[usize], signature: &[u8; 96], message: &[u8]) -> u64 {
            if ranks.iter().any(|&r| r >= self.keys.len()) {
                return 0;
            }
            let key: G1Projective = ranks.iter().map(|&r| self.keys[r]).sum();
            match Option::<G2Affine>::from(G2Affine::from_compressed(signature)) {
                Some(s) if holds(&key, message, &s.into()) => ranks.iter().map(|&r| self.stakes[r]).sum(),
                _ => 0,
            }
        }

        /// Is the block final, with these ranks having voted for it and these that its slot is final (none: only the first vote)?
        fn claim(&self, for_it: &[usize], is_final: &[usize], block: &[u8], signed: (u64, u16), read: (u64, u16), known: bool) -> bool {
            let total: u64 = if known { self.stakes.iter().sum() } else { 0 };
            let for_block = self.signed_stake(for_it, &self.signed_by(for_it, &vote(1, signed.0, block, signed.1)), &vote(1, read.0, block, read.1));
            let for_slot = self.signed_stake(is_final, &self.signed_by(is_final, &vote(2, signed.0, &[], signed.1)), &vote(2, read.0, &[], read.1));
            if total == 0 {
                false
            } else if is_final.is_empty() {
                5 * for_block >= 4 * total
            } else {
                5 * for_slot >= 3 * total && 5 * for_block >= 3 * total
            }
        }
    }

    fn reading(bytes: &[u8; 96]) -> &'static str {
        if bool::from(G2Affine::from_compressed(bytes).is_some()) { "accepted" } else { "rejected" }
    }

    pub fn report() {
        let g = G1Projective::generator();
        println!("generator        {}", hex(&g.to_affine().to_compressed()));
        println!("twice it         {}", hex(&(g + g).to_affine().to_compressed()));
        println!("minus it         {}", hex(&(-g).to_affine().to_compressed()));
        let none = G2Projective::identity().to_affine().to_compressed();
        println!("no point         {}", hex(&none));
        for text in ["", "abc", "a vote"] {
            println!("point of \"{text}\": {}", hex(&point(text.as_bytes()).to_affine().to_compressed()));
        }
        let secrets: Vec<Scalar> = [
            [1, 0, 0, 0],
            [0x1234567890abcdef, 0x0fedcba098765432, 7, 0],
            [0x0102030405060708, 0x1112131415161718, 0x2122232425262728, 0x3132333435363738],
            [42, 42, 42, 42],
        ]
        .iter()
        .map(|words| Scalar::from_u64s_le(words).unwrap())
        .collect();
        let v = Validators { keys: secrets.iter().map(|s| g * s).collect(), secrets, stakes: vec![40, 30, 20, 10] };
        let block: Vec<u8> = (0..32u32).map(|i| (7 * i + 1) as u8).collect();
        let (slot, version) = (474737400u64, 50093u16);
        let for_block = vote(1, slot, &block, version);
        let for_slot = vote(2, slot, &[], version);
        println!("a vote for a block:     {}", hex(&for_block));
        println!("a vote a slot is final: {}", hex(&for_slot));
        for k in 0..4 {
            let signature = point(&for_block) * v.secrets[k];
            let bytes = signature.to_affine().to_compressed();
            println!("validator {k}: key {}", hex(&v.keys[k].to_affine().to_compressed()));
            println!("  signs the block {}", hex(&bytes));
            if k == 1 {
                println!(
                    "  which {}; for the other vote it {}; read back: {}",
                    verdict(holds(&v.keys[k], &for_block, &signature)),
                    verdict(holds(&v.keys[k], &for_slot, &signature)),
                    G2Affine::from_compressed(&bytes).unwrap() == signature.to_affine()
                );
            }
        }
        let all_keys: G1Projective = v.keys.iter().sum();
        println!("all keys added   {}, stake {}", hex(&all_keys.to_affine().to_compressed()), v.stakes.iter().sum::<u64>());
        let all = [0, 1, 2, 3];
        let stake = |named: &[usize], signed: &[usize]| v.signed_stake(named, &v.signed_by(signed, &for_block), &for_block);
        println!("all four sign:   {}", hex(&v.signed_by(&all, &for_block)));
        println!("stake behind it: {}; behind 0, 1 and 3: {}", stake(&all, &all), stake(&[0, 1, 3], &[0, 1, 3]));
        println!(
            "a bitmap naming one who did not sign: {}; the other vote: {}",
            stake(&all, &[0, 1, 2]),
            v.signed_stake(&all, &v.signed_by(&all, &for_block), &for_slot)
        );
        println!("a rank that does not exist: {}; nobody: {}", stake(&[0, 1, 2, 5], &[0, 1, 2]), v.signed_stake(&[], &none, &for_block));
        let claim = |for_it: &[usize], is_final: &[usize]| v.claim(for_it, is_final, &block, (slot, version), (slot, version), true);
        println!("80 of 100 vote for the block: final {}; 70: {}", claim(&[0, 1, 3], &[]), claim(&[0, 1], &[]));
        println!("60 for the block and 60 that the slot is final: {}; 60 and 50: {}", claim(&[0, 2], &[1, 2, 3]), claim(&[0, 2], &[0, 3]));
        println!(
            "another shred version: {}; no validators known: {}",
            v.claim(&all, &[], &block, (slot, version), (slot, version + 1), true),
            v.claim(&all, &[], &block, (slot, version), (slot, version), false)
        );
        let stray: Vec<u8> = (0..96).map(|i| u8::from_str_radix(&STRAY[2 * i..2 * i + 2], 16).unwrap()).collect();
        let stray: [u8; 96] = stray.try_into().unwrap();
        println!("a point outside the group: {}", hex(&stray));
        let mut changed = v.signed_by(&all, &for_block);
        changed[95] = 0;
        println!(
            "read as a signature: {} (it is on the curve: {}); a byte of a good one changed: {}",
            reading(&stray),
            bool::from(G2Affine::from_compressed_unchecked(&stray).is_some()),
            reading(&changed)
        );
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        #[cfg(feature = "bls")]
        Some("bls") => bls::report(),
        Some("versions") if args.len() >= 3 => versions(&args[2..]),
        Some("builtins") if args.len() == 4 => builtins(&args[2], &args[3]),
        Some("anchor") if args.len() >= 3 => args[2..].iter().for_each(|file| anchor(file)),
        Some("transaction") if args.len() == 4 => transaction(&args[2], &args[3]),
        _ => {
            eprintln!("usage: oracle anchor anchor_vault.so\n       oracle transaction sysvar_probe.so counter.so\n       oracle versions probe.so...");
            std::process::exit(2);
        }
    }
}
