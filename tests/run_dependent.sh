#!/usr/bin/env bash
# Runs the dependent-types suite:
#   * every tests/dependent/*.iota must FAIL to type-check (and must not crash the compiler),
#     except those whose first line says `# expect: compiles`, which must compile;
#   * every example below must build, run, and print the expected output.
# Usage: tests/run_dependent.sh [path/to/iota]     (default: target/debug/iota)
set -u
cd "$(dirname "$0")/.."
IOTA="${1:-target/debug/iota}"
pass=0
fail=0

for f in tests/dependent/*.iota; do
	out=$("$IOTA" "$f" --emit ir 2>&1)
	code=$?
	want=$(head -1 "$f" | sed 's/^# *//')
	if echo "$want" | grep -q "^expect: compiles"; then
		# a regression test for something that must keep working
		if [ $code -eq 0 ]; then
			pass=$((pass + 1))
		else
			echo "FAIL  $f: should compile ($want)"
			fail=$((fail + 1))
		fi
	elif [ $code -eq 0 ]; then
		echo "FAIL  $f: compiled, but should be rejected ($want)"
		fail=$((fail + 1))
	elif echo "$out" | grep -qi "internal compiler error\|panicked"; then
		echo "FAIL  $f: the compiler crashed instead of reporting an error"
		fail=$((fail + 1))
	else
		pass=$((pass + 1))
	fi
done

# example:expected output (first line)
while IFS=: read -r name expected; do
	[ -z "$name" ] && continue
	f="examples/$name.iota"
	exe="build/$name"
	if ! "$IOTA" "$f" -o "$exe" >/dev/null 2>&1; then
		echo "FAIL  $f: does not compile"
		fail=$((fail + 1))
		continue
	fi
	got=$("$exe" 2>&1 | head -1)
	if [ "$got" = "$expected" ]; then
		pass=$((pass + 1))
	else
		echo "FAIL  $f: printed '$got', expected '$expected'"
		fail=$((fail + 1))
	fi
done <<'EXAMPLES'
dep_gadt:11
dep_vec:13
dep_expr:15
dep_snat:24
dep_proofs:6
dep_exists:63
dep_sigma:14
dep_bignat:2000000
dep_sigma_class:13
dep_promote:27
dep_sigma_more:33
dep_bool:7
dep_induction:double n = n + n, by induction
dep_const:36
dep_linear:41
dep_linear_io:write
dep_linear_class:105
EXAMPLES

echo "passed: $pass, failed: $fail"
[ $fail -eq 0 ]
