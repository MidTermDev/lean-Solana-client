//! The reference for tests/anchor.lean.
//!
//! Runs the same instructions, on the same accounts at the same addresses,
//! on Agave's program runtime (through LiteSVM), and prints the same report.
//! `make oracle` builds this, runs it, and compares its output with
//! tests/expected/anchor.txt, which the Lean virtual machine must reproduce:
//! results, compute units, logs and account contents.
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

fn main() {
    let program = std::env::args().nth(1).expect("usage: oracle anchor_vault.so");
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
