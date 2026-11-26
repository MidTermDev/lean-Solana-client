#!/bin/sh
# Apply a signed transaction to an account, locally.
#
# The transaction below sets a compute-unit price and transfers 1.5 SOL. It
# is a real, signed, serialized transaction of the kind a wallet produces;
# `leansol tx` checks its signature, charges its fee (5,000 lamports for the
# signature, 120 for the priority it bids), runs both instructions and shows
# what changed. The only account that must be supplied is the one paying.
#
#   make && examples/transaction.sh
set -eu
cd "$(dirname "$0")/.."
${LEANSOL:-build/leansol} tx \
  Ad3wCIYBguRqGrGVw1KtF7pkrwL0rE3NyewqG+00G3eQ9F5iW4COROhDTWIGlFpxn5GRw1rFce26sOGIeugE8QQBAAIExCA1t81mmFK1GkmQzOCWoPxDUjC33/EQ1NqPOrrWO/fVv0o/zOcXsDiLzCdJ68FIrZlpsj9F7htgX9WHeFdqxAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwZGb+UhFzL/7K26csOb57yM5bvF9xJrLEObOkAAAAA5W/cn+arF6AkRWRBz/PnIJvQogEExygib66OGlCF0mgIDAAkDIE4AAAAAAAACAgABDAIAAAAAL2hZAAAAAA== \
  --account ECbPvoRPTunYYuu6iCP8gK4GzGX4nc5rPsUpAKoT6vV4:system:5000000000:
