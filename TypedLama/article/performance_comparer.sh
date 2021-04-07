LAMAC="../../src/lamac -tc -i"

# https://unix.stackexchange.com/questions/12068/how-to-measure-time-of-program-execution-and-store-that-inside-a-variable
utime="$( TIMEFORMAT='%lU';time ( ls ) 2>&1 1>/dev/null )"

echo "+----+----------+----------+"
echo "| n  | Untyped  | Typed    |"
echo "+----+----------+----------+"
max=50
# https://stackoverflow.com/questions/1445452/shell-script-for-loop-syntax
for (( i=10; i <= $max; ++i ))
do
  utime1="$( TIMEFORMAT='%lU';time ( echo $i | $LAMAC fibonacci_no_typecheck.lama 2>/dev/null) 2>&1 1>/dev/null )"
  utime2="$( TIMEFORMAT='%lU';time ( echo $i | $LAMAC fibonacci_typecheck.lama 2>/dev/null) 2>&1 1>/dev/null )"
    echo "| $i | $utime1 | $utime2 |"
done
echo "+----+----------+----------+"