#!/bin/sh
# A program written in Lean calls the SPL token programs, from the command line.
#
# Sets up two tokens with the real token programs, creates a pool in
# lean-svm's AMM, and adds liquidity: one instruction in which the AMM calls
# the classic Token program and Token-2022 to move the user's tokens into
# the pool's vaults. Every step is one `leansol run`; `--full` prints
# account data so the next step can take it as input.
#
#   make && examples/amm.sh
set -eu
cd "$(dirname "$0")/.."
RUN="${LEANSOL:-build/leansol} run"
P=tests/programs
TOKEN=TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA
TOKEN22=TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb

addr()  { printf %s "$1" | sha256sum | cut -c1-64; }    # the stand-in address `leansol run` gives a name
zeros() { printf "%0$(( $1 * 2 ))d" 0; }
le64()  { printf '%016x' "$1" | fold -w2 | tac | tr -d '\n'; }
data()  { awk -v n="$1" '$1 == "account" && $2 == n { print $6 }'; }   # one account's data from a run

# --- two mints: A (6 decimals) under Token, B (9 decimals) under Token-2022.  InitializeMint2 = 20
mintA=$($RUN $P/pinocchio_token_program.so --program-id $TOKEN --full --data "1406$(addr payer)00" \
          --account "mintA:program:10000000:$(zeros 82):w" | data mintA)
mintB=$($RUN $P/spl_token_2022-10.0.0.so --program-id $TOKEN22 --full --data "1409$(addr payer)00" \
          --account "mintB:program:10000000:$(zeros 82):w" | data mintB)

# --- token accounts: the user's and the pool's, for each token.  InitializeAccount3 = 18
open() {  # open NAME OWNER PROGRAM.so PROGRAM-ID MINT-NAME MINT-DATA
  $RUN "$3" --program-id "$4" --full --data "12$(addr "$2")" \
    --account "$1:program:10000000:$(zeros 165):w" --account "$5:program:10000000:$6" | data "$1"
}
userA=$(open userA user $P/pinocchio_token_program.so $TOKEN mintA "$mintA")
vaultA=$(open vaultA pool-authority $P/pinocchio_token_program.so $TOKEN mintA "$mintA")
userB=$(open userB user $P/spl_token_2022-10.0.0.so $TOKEN22 mintB "$mintB")
vaultB=$(open vaultB pool-authority $P/spl_token_2022-10.0.0.so $TOKEN22 mintB "$mintB")

# --- mint 2,000,000 of each to the user.  MintTo = 7; the mint authority signs
out=$($RUN $P/pinocchio_token_program.so --program-id $TOKEN --full --data "07$(le64 2000000)" \
        --account "mintA:program:10000000:$mintA:w" --account "userA:program:10000000:$userA:w" --account payer:system:1::s)
mintA=$(echo "$out" | data mintA); userA=$(echo "$out" | data userA)
out=$($RUN $P/spl_token_2022-10.0.0.so --program-id $TOKEN22 --full --data "07$(le64 2000000)" \
        --account "mintB:program:10000000:$mintB:w" --account "userB:program:10000000:$userB:w" --account payer:system:1::s)
mintB=$(echo "$out" | data mintB); userB=$(echo "$out" | data userB)

# --- the pool: instruction 0 = init (bump, decimals of A and B, fee in basis points)
pool=$($RUN $P/amm.so --full --data "00ff06091e00" --account "pool:program:10000000:$(zeros 120):w" \
         --account "vaultA:$TOKEN:10000000:$vaultA" --account "vaultB:$TOKEN22:10000000:$vaultB" | data pool)

# --- add liquidity: instruction 1 = amounts of A and B, minimum shares. The AMM calls both token programs.
echo "\$ leansol run amm.so --program Token=… --program Token-2022=… --data 01… (add 1,000,000 A + 1,000,000 B)"
$RUN $P/amm.so --program $TOKEN=$P/pinocchio_token_program.so --program $TOKEN22=$P/spl_token_2022-10.0.0.so \
  --data "01$(le64 1000000)$(le64 1000000)$(le64 999999)" \
  --account user:system:1000000000::s \
  --account "pool:program:10000000:$pool:w" \
  --account "mintA:$TOKEN:10000000:$mintA" --account "mintB:$TOKEN22:10000000:$mintB" \
  --account "vaultA:$TOKEN:10000000:$vaultA:w" --account "vaultB:$TOKEN22:10000000:$vaultB:w" \
  --account "userA:$TOKEN:10000000:$userA:w" --account "userB:$TOKEN22:10000000:$userB:w" \
  --account $TOKEN --account $TOKEN22
