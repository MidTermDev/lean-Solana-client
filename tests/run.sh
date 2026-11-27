#!/bin/sh
# Compiles every tests/*.lean with leanc, runs it, and compares the output
# with tests/expected/. The expected files were produced by the official
# Lean toolchain, so a pass means leanc agrees with the reference
# implementation on that program.
#
#   tests/run.sh            run the suite (needs only build/leanc)
#   tests/run.sh --oracle   additionally re-run each test under the official
#                           toolchain (needs `lake` on PATH) and compare
set -u
cd "$(dirname "$0")/.."
LEANC=build/leanc
ORACLE=0
[ "${1:-}" = "--oracle" ] && ORACLE=1
# Tests that use raw syscalls only exist as machine code: the official
# interpreter has no implementation of the leanc_* intrinsics.
NATIVE_ONLY="ipc panic inplace store"
mkdir -p build/tests
pass=0
fail=0

for src in tests/*.lean; do
  name=$(basename "$src" .lean)
  bin=build/tests/$name
  if ! $LEANC -I rt -I lib -o "$bin" "$src" 2> build/tests/$name.err; then
    echo "FAIL  $name (does not compile)"; cat build/tests/$name.err; fail=$((fail + 1)); continue
  fi
  "$bin" > build/tests/$name.out 2> build/tests/$name.stderr
  code=$?
  if [ "$name" = panic ]; then
    if [ $code -eq 101 ] && grep -q "index out of bounds (line 7)" build/tests/$name.stderr &&
       [ "$(cat build/tests/$name.out)" = "before" ]; then
      echo "ok    $name (aborted with a bounds panic, as it must)"; pass=$((pass + 1))
    else
      echo "FAIL  $name (expected exit 101 and a bounds panic, got exit $code)"; fail=$((fail + 1))
    fi
    continue
  fi
  if [ $code -ne 0 ] || ! cmp -s build/tests/$name.out tests/expected/$name.txt; then
    echo "FAIL  $name (exit $code)"; diff build/tests/$name.out tests/expected/$name.txt | head -10
    fail=$((fail + 1)); continue
  fi
  note=""
  if [ $ORACLE -eq 1 ]; then
    case " $NATIVE_ONLY " in
    *" $name "*) note=" (native only)" ;;
    *)
      if lake env lean --run "$src" 2>/dev/null | cmp -s - tests/expected/$name.txt; then
        note=" (official Lean agrees)"
      else
        echo "FAIL  $name (official Lean output differs from tests/expected/$name.txt)"
        fail=$((fail + 1)); continue
      fi ;;
    esac
  fi
  echo "ok    $name$note"; pass=$((pass + 1))
done

echo "$pass passed, $fail failed"
[ $fail -eq 0 ]
