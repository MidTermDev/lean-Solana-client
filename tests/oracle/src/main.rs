//! The reference for tests/anchor.lean and tests/transaction.lean.
//!
//! Runs the same instructions and transactions, on the same accounts at the
//! same addresses, on Agave's program runtime (through LiteSVM), and prints
//! the same report. `make oracle` builds this, runs it, and compares its
//! output with tests/expected/anchor.txt and tests/expected/transaction.txt,
//! which the Lean virtual machine must reproduce: results, fees, compute
//! units, logs and account contents.
//!
//!     oracle anchor anchor_vault.so
//!     oracle transaction sysvar_probe.so counter.so
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
    solana_message::Message,
    solana_signer::Signer,
    solana_transaction::{Transaction, TransactionError},
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
    fn send(&mut self, label: &str, tx: Transaction) {
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("anchor") if args.len() == 3 => anchor(&args[2]),
        Some("transaction") if args.len() == 4 => transaction(&args[2], &args[3]),
        _ => {
            eprintln!("usage: oracle anchor anchor_vault.so\n       oracle transaction sysvar_probe.so counter.so");
            std::process::exit(2);
        }
    }
}
