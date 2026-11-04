#!/usr/bin/env bash
# Compiler tests
#
#   tests/pass/<area>/<name>.iota   must compile and run, exit 0, and print exactly the lines
#                                   given by its `# out: <line>` header comments (none: no
#                                   output is checked). `# in: <line>` lines are fed to stdin.
#                                   Each program is built twice, with the normal optimizer and
#                                   with `--opt-mode aggressive`, and both must print the same.
#   tests/pass/<area>/lib/          helper modules imported by the tests; not run themselves
#   tests/fail/<area>/<name>.iota   must be REJECTED at compile time with an error, and the
#                                   compiler must not crash. An optional `# error: <text>`
#                                   header requires <text> to appear in the diagnostics.
#   tests/trap/<name>.iota          must compile, then stop at run time with an error exit
#                                   status (1..127).
#
# Usage: tests/run_tests.sh [path/to/iota] [filter]
#   filter: only run tests whose path contains this text (e.g. `matching` or `fail/types`).
set -u
cd "$(dirname "$0")/.."
IOTA="${1:-target/debug/iota}"
FILTER="${2:-}"
OUT=build/tests
mkdir -p "$OUT"
pass=0
fail=0
crash_re='internal compiler error|panicked|RUST_BACKTRACE'

selected() { [ -z "$FILTER" ] || [[ "$1" == *"$FILTER"* ]]; }
note() { echo "FAIL  $1: $2"; fail=$((fail + 1)); }

for f in tests/pass/*/*.iota; do
	selected "$f" || continue
	want=$(grep '^# out:' "$f" | sed 's/^# out: \{0,1\}//')
	has_out=$(grep -c '^# out:' "$f")
	input=$(grep '^# in:' "$f" | sed 's/^# in: \{0,1\}//')
	base=$(echo "$f" | sed 's|^tests/pass/||; s|/|_|g; s|\.iota$||')
	for mode in default aggressive; do
		exe="$OUT/$base.$mode"
		flags=()
		[ "$mode" = aggressive ] && flags=(--opt-mode aggressive)
		if ! msg=$("$IOTA" "$f" -o "$exe" ${flags[@]+"${flags[@]}"} 2>&1); then
			note "$f [$mode]" "does not compile"
			echo "$msg" | head -5 | sed 's/^/        /'
			continue
		fi
		got=$(printf '%s' "$input" | timeout 20 "$exe" 2>&1)
		code=$?
		if [ $code -ne 0 ]; then
			note "$f [$mode]" "exited with status $code"
		elif [ "$has_out" -gt 0 ] && [ "$got" != "$want" ]; then
			note "$f [$mode]" "wrong output"
			diff <(echo "$want") <(echo "$got") | head -6 | sed 's/^/        /'
		else
			pass=$((pass + 1))
		fi
	done
done

for f in tests/fail/*/*.iota; do
	selected "$f" || continue
	out=$("$IOTA" "$f" --emit ir 2>&1)
	code=$?
	want=$(grep -m1 '^# error:' "$f" | sed 's/^# error: \{0,1\}//')
	if [ $code -eq 0 ]; then
		note "$f" "compiled, but should be rejected ($(head -1 "$f" | sed 's/^# *//'))"
	elif echo "$out" | grep -Eq "$crash_re"; then
		note "$f" "the compiler crashed instead of reporting an error"
	elif [ -n "$want" ] && ! echo "$out" | grep -qF -- "$want"; then
		note "$f" "the error does not mention '$want'"
	else
		pass=$((pass + 1))
	fi
done

for f in tests/trap/*.iota; do
	selected "$f" || continue
	exe="$OUT/trap_$(basename "$f" .iota)"
	if ! msg=$("$IOTA" "$f" -o "$exe" 2>&1); then
		note "$f" "does not compile"
		echo "$msg" | head -5 | sed 's/^/        /'
		continue
	fi
	timeout 20 "$exe" >/dev/null 2>&1 </dev/null
	code=$?
	if [ $code -ge 1 ] && [ $code -le 127 ]; then
		pass=$((pass + 1))
	else
		note "$f" "exit status $code (wanted a clean error exit, 1..127)"
	fi
done

echo "passed: $pass, failed: $fail"
[ $fail -eq 0 ]
