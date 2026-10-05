# Laws 2 and 3: decimal and hexadecimal numerals read back as written.
#
# show(n) writes the little-endian digit list count(n, [0]) most significant
# digit first; read folds those chars into an accumulator. horner(b, ds, a) is
# the accumulator after reading the digits of ds starting from a (with no
# saturation), so horner(b, ds, 0) is the value of ds. The proof:
#   - count(n, [0]) is nonempty, holds digits below the base, and has value n
#     (each inc adds one);
#   - reading digits_text(ds, acc) from Some{a} reads acc from
#     Some{horner(b, ds, a)}, as long as horner(b, ds, a) <= LIMIT (then every
#     intermediate accumulator is <= LIMIT too, so push never saturates);
#   - bound accepts the value, which is n <= LIMIT.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/num.bend as N

def NL() -> Data:
  List<&2, Nat>

def MN() -> Data:
  Maybe<&2, Nat>

# Bool facts
# ----------

def bdisc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : bdisc(_)
  Unit{}

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(e))

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true(e))

# Nat arithmetic
# --------------

def add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# Nat order (Nat.is_le as a Bool fact)
# ------------------------------------

def le_zero(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_succ(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, false_true(h))
    case 1n+p 1n+q:
      le_succ(p, q, h)

def le_weak(+a: Nat, +y: Nat, k: Nat, h: {Nat.is_le(a, y) == True{} : Bool}) -> {Nat.is_le(a, Nat.add(k, y)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n++j:
      le_succ(a, Nat.add(j, y), le_weak(a, y, j, h))

def le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, false_true(h1))
    case 1n+p 0n 1n+r:
      Empty.absurd({Nat.is_le(1n+p, 1n+r) == True{} : Bool}, false_true(h1))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, false_true(h2))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, h1, h2)

# A number is at most its value with one more digit, in any base 1n+b.
def le_push(x: Nat, +b: Nat, +d: Nat) -> {Nat.is_le(x, Nat.add(Nat.mul(x, 1n+b), d)) == True{} : Bool}:
  match x:
    case 0n:
      le_zero(d)
    case 1n++p:
      %add_assoc(b, Nat.mul(p, 1n+b), d) : {Nat.is_le(p, _) == True{} : Bool}
      le_weak(p, Nat.add(Nat.mul(p, 1n+b), d), b, le_push(p, b, d))

# Horner value
# ------------

# The accumulator after reading the digits of ds (little-endian, so read
# most significant first) from a, in base b, without saturation.
def horner(+b: Nat, ds: NL(), a: Nat) -> Nat:
  match ds:
    case Nil{}:
      a
    case Con{d, t}:
      Nat.add(Nat.mul(horner(b, t, a), b), d)

# Every digit of ds is at most top.
def digits_ok(+top: Nat, ds: NL()) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      Bool.and(Nat.is_le(d, top), digits_ok(top, t))

def is_con(ds: NL()) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      True{}


def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# Decimal
# -------

def dec_read_scon(t: NL(), c: Char, a: String) -> {N.read(N.digits_text(t, SCon{c, a})) == N.bound(N.dec_read.go(N.digits_text(t, SCon{c, a}), Some{0n})) : MN()}:
  match t:
    case Nil{}:
      {==}
    case Con{d, r}:
      dec_read_scon(r, N.digit_char(d), SCon{c, a})

def dec_read_con(ds: NL(), e: {is_con(ds) == True{} : Bool}) -> {N.read(N.digits_text(ds, SNil{})) == N.bound(N.dec_read.go(N.digits_text(ds, SNil{}), Some{0n})) : MN()}:
  match ds:
    case Nil{}:
      Empty.absurd({N.read(SNil{}) == N.bound(N.dec_read.go(SNil{}, Some{0n})) : MN()}, false_true(e))
    case Con{d, t}:
      dec_read_scon(t, N.digit_char(d), SNil{})

# The char of a digit d <= 9 reads back as d.
def dec_char(d: Nat, e: {Nat.is_le(d, 9n) == True{} : Bool}) -> {N.dec_value(B.char_class(N.digit_char(d))) == Some{d} : MN()}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+k:
      Empty.absurd({N.dec_value(B.char_class(N.digit_char(10n+k))) == Some{10n+k} : MN()}, false_true(e))

# inc keeps the digits below the base.
def dec_inc_ok(ds: NL(), e: {digits_ok(9n, ds) == True{} : Bool}) -> {digits_ok(9n, N.dec_inc(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case 0n:
          e
        case 1n:
          e
        case 2n:
          e
        case 3n:
          e
        case 4n:
          e
        case 5n:
          e
        case 6n:
          e
        case 7n:
          e
        case 8n:
          e
        case 9n:
          dec_inc_ok(t, e)
        case 10n+k:
          Empty.absurd({digits_ok(9n, N.dec_inc(Con{10n+k, t})) == True{} : Bool}, false_true(e))

# inc never answers [].
def dec_inc_con(ds: NL()) -> {is_con(N.dec_inc(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n:
          {==}
        case 9n:
          {==}
        case 10n+k:
          {==}

# inc adds one to the value.
def dec_inc_val(ds: NL(), e: {digits_ok(9n, ds) == True{} : Bool}) -> {horner(10n, N.dec_inc(ds), 0n) == 1n+horner(10n, ds, 0n) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      match d:
        case 0n:
          add_succ(Nat.mul(horner(10n, t, 0n), 10n), 0n)
        case 1n:
          add_succ(Nat.mul(horner(10n, t, 0n), 10n), 1n)
        case 2n:
          add_succ(Nat.mul(horner(10n, t, 0n), 10n), 2n)
        case 3n:
          add_succ(Nat.mul(horner(10n, t, 0n), 10n), 3n)
        case 4n:
          add_succ(Nat.mul(horner(10n, t, 0n), 10n), 4n)
        case 5n:
          add_succ(Nat.mul(horner(10n, t, 0n), 10n), 5n)
        case 6n:
          add_succ(Nat.mul(horner(10n, t, 0n), 10n), 6n)
        case 7n:
          add_succ(Nat.mul(horner(10n, t, 0n), 10n), 7n)
        case 8n:
          add_succ(Nat.mul(horner(10n, t, 0n), 10n), 8n)
        case 9n:
          %Equal.sym(Nat, Nat.add(Nat.mul(horner(10n, N.dec_inc(t), 0n), 10n), 0n), Nat.mul(horner(10n, N.dec_inc(t), 0n), 10n), add_zero(Nat.mul(horner(10n, N.dec_inc(t), 0n), 10n))) : {_ == 1n+Nat.add(Nat.mul(horner(10n, t, 0n), 10n), 9n) : Nat}
          %Equal.sym(Nat, horner(10n, N.dec_inc(t), 0n), 1n+horner(10n, t, 0n), dec_inc_val(t, e)) : {Nat.mul(_, 10n) == 1n+Nat.add(Nat.mul(horner(10n, t, 0n), 10n), 9n) : Nat}
          %add_comm(Nat.mul(horner(10n, t, 0n), 10n), 9n) : {1n+_ == 1n+Nat.add(Nat.mul(horner(10n, t, 0n), 10n), 9n) : Nat}
          {==}
        case 10n+k:
          Empty.absurd({horner(10n, N.dec_inc(Con{10n+k, t}), 0n) == 1n+horner(10n, Con{10n+k, t}, 0n) : Nat}, false_true(e))

def dec_count_ok(n: Nat, +ds: NL(), e: {digits_ok(9n, ds) == True{} : Bool}) -> {digits_ok(9n, N.dec_count(n, ds)) == True{} : Bool}:
  match n:
    case 0n:
      e
    case 1n+p:
      dec_count_ok(p, N.dec_inc(ds), dec_inc_ok(ds, e))

def dec_count_con(n: Nat, +ds: NL(), e: {is_con(ds) == True{} : Bool}) -> {is_con(N.dec_count(n, ds)) == True{} : Bool}:
  match n:
    case 0n:
      e
    case 1n+p:
      dec_count_con(p, N.dec_inc(ds), dec_inc_con(ds))

# n increments add n to the value.
def dec_count_val(n: Nat, +ds: NL(), +e: {digits_ok(9n, ds) == True{} : Bool}) -> {horner(10n, N.dec_count(n, ds), 0n) == Nat.add(n, horner(10n, ds, 0n)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, horner(10n, N.dec_count(p, N.dec_inc(ds)), 0n), Nat.add(p, horner(10n, N.dec_inc(ds), 0n)), dec_count_val(p, N.dec_inc(ds), dec_inc_ok(ds, e))) : {_ == 1n+Nat.add(p, horner(10n, ds, 0n)) : Nat}
      %Equal.sym(Nat, horner(10n, N.dec_inc(ds), 0n), 1n+horner(10n, ds, 0n), dec_inc_val(ds, e)) : {Nat.add(p, _) == 1n+Nat.add(p, horner(10n, ds, 0n)) : Nat}
      add_succ(p, horner(10n, ds, 0n))

# Reading the text of ds from Some{a} reaches Some{horner(ds, a)} when that
# is at most LIMIT (and so is every accumulator on the way).
def dec_fold(ds: NL(), +acc: String, +a: Nat, +ok: {digits_ok(9n, ds) == True{} : Bool}, lim: {Nat.is_le(horner(10n, ds, a), N.LIMIT()) == True{} : Bool})
  -> {N.dec_read.go(N.digits_text(ds, acc), Some{a}) == N.dec_read.go(acc, Some{horner(10n, ds, a)}) : MN()}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      okd = and_l(Nat.is_le(d, 9n), digits_ok(9n, t), ok)
      okt = and_r(Nat.is_le(d, 9n), digits_ok(9n, t), ok)
      +limt = le_trans(horner(10n, t, a), Nat.add(Nat.mul(horner(10n, t, a), 10n), d), N.LIMIT(), le_push(horner(10n, t, a), 9n, d), lim)
      %Equal.sym(MN(), N.dec_read.go(N.digits_text(t, SCon{N.digit_char(d), acc}), Some{a}), N.dec_read.go(SCon{N.digit_char(d), acc}, Some{horner(10n, t, a)}), dec_fold(t, SCon{N.digit_char(d), acc}, a, okt, limt)) : {_ == N.dec_read.go(acc, Some{Nat.add(Nat.mul(horner(10n, t, a), 10n), d)}) : MN()}
      %Equal.sym(MN(), N.dec_value(B.char_class(N.digit_char(d))), Some{d}, dec_char(d, okd)) : {N.dec_read.go(acc, N.read.step(Some{horner(10n, t, a)}, 10n, _)) == N.dec_read.go(acc, Some{Nat.add(Nat.mul(horner(10n, t, a), 10n), d)}) : MN()}
      %Equal.sym(Bool, Nat.is_le(horner(10n, t, a), N.LIMIT()), True{}, limt) : {N.dec_read.go(acc, Some{N.push.pick(_, horner(10n, t, a), 10n, d)}) == N.dec_read.go(acc, Some{Nat.add(Nat.mul(horner(10n, t, a), 10n), d)}) : MN()}
      {==}

# The digits of n have value n.
def dec_digits_val(+n: Nat) -> {horner(10n, N.dec_count(n, [0n]), 0n) == n : Nat}:
  Equal.trans(Nat, horner(10n, N.dec_count(n, [0n]), 0n), Nat.add(n, 0n), n, dec_count_val(n, [0n], {==}), add_zero(n))

def dec_digits_lim(+n: Nat, e: {Nat.is_le(n, N.LIMIT()) == True{} : Bool}) -> {Nat.is_le(horner(10n, N.dec_count(n, [0n]), 0n), N.LIMIT()) == True{} : Bool}:
  %Equal.sym(Nat, horner(10n, N.dec_count(n, [0n]), 0n), n, dec_digits_val(n)) : {Nat.is_le(_, N.LIMIT()) == True{} : Bool}
  e

def Laws.dec_roundtrip(n, e0):
  +e = e0
  %Equal.sym(MN(), N.read(N.digits_text(N.dec_count(n, [0n]), SNil{})), N.bound(N.dec_read.go(N.digits_text(N.dec_count(n, [0n]), SNil{}), Some{0n})), dec_read_con(N.dec_count(n, [0n]), dec_count_con(n, [0n], {==}))) : {_ == Some{n} : MN()}
  %Equal.sym(MN(), N.dec_read.go(N.digits_text(N.dec_count(n, [0n]), SNil{}), Some{0n}), N.dec_read.go(SNil{}, Some{horner(10n, N.dec_count(n, [0n]), 0n)}), dec_fold(N.dec_count(n, [0n]), SNil{}, 0n, dec_count_ok(n, [0n], {==}), dec_digits_lim(n, e))) : {N.bound(_) == Some{n} : MN()}
  %Equal.sym(Nat, horner(10n, N.dec_count(n, [0n]), 0n), n, dec_digits_val(n)) : {N.bound(Some{_}) == Some{n} : MN()}
  %Equal.sym(Bool, Nat.is_le(n, N.LIMIT()), True{}, e) : {N.bound.pick(_, n) == Some{n} : MN()}
  {==}

# Hexadecimal
# -----------

def hex_read_scon(t: NL(), c: Char, a: String) -> {N.hex_read(N.digits_text(t, SCon{c, a})) == N.bound(N.hex_read.go(N.digits_text(t, SCon{c, a}), Some{0n})) : MN()}:
  match t:
    case Nil{}:
      {==}
    case Con{d, r}:
      hex_read_scon(r, N.digit_char(d), SCon{c, a})

def hex_read_con(ds: NL(), e: {is_con(ds) == True{} : Bool}) -> {N.hex_read(N.digits_text(ds, SNil{})) == N.bound(N.hex_read.go(N.digits_text(ds, SNil{}), Some{0n})) : MN()}:
  match ds:
    case Nil{}:
      Empty.absurd({N.hex_read(SNil{}) == N.bound(N.hex_read.go(SNil{}, Some{0n})) : MN()}, false_true(e))
    case Con{d, t}:
      hex_read_scon(t, N.digit_char(d), SNil{})

# The char of a digit d <= 15 reads back as d.
def hex_char(d: Nat, e: {Nat.is_le(d, 15n) == True{} : Bool}) -> {N.hex_value(B.char_class(N.digit_char(d))) == Some{d} : MN()}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n+k:
      Empty.absurd({N.hex_value(B.char_class(N.digit_char(16n+k))) == Some{16n+k} : MN()}, false_true(e))

# inc keeps the digits below the base.
def hex_inc_ok(ds: NL(), e: {digits_ok(15n, ds) == True{} : Bool}) -> {digits_ok(15n, N.hex_inc(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case 0n:
          e
        case 1n:
          e
        case 2n:
          e
        case 3n:
          e
        case 4n:
          e
        case 5n:
          e
        case 6n:
          e
        case 7n:
          e
        case 8n:
          e
        case 9n:
          e
        case 10n:
          e
        case 11n:
          e
        case 12n:
          e
        case 13n:
          e
        case 14n:
          e
        case 15n:
          hex_inc_ok(t, e)
        case 16n+k:
          Empty.absurd({digits_ok(15n, N.hex_inc(Con{16n+k, t})) == True{} : Bool}, false_true(e))

# inc never answers [].
def hex_inc_con(ds: NL()) -> {is_con(N.hex_inc(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n:
          {==}
        case 9n:
          {==}
        case 10n:
          {==}
        case 11n:
          {==}
        case 12n:
          {==}
        case 13n:
          {==}
        case 14n:
          {==}
        case 15n:
          {==}
        case 16n+k:
          {==}

# inc adds one to the value.
def hex_inc_val(ds: NL(), e: {digits_ok(15n, ds) == True{} : Bool}) -> {horner(16n, N.hex_inc(ds), 0n) == 1n+horner(16n, ds, 0n) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      match d:
        case 0n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 0n)
        case 1n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 1n)
        case 2n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 2n)
        case 3n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 3n)
        case 4n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 4n)
        case 5n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 5n)
        case 6n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 6n)
        case 7n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 7n)
        case 8n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 8n)
        case 9n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 9n)
        case 10n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 10n)
        case 11n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 11n)
        case 12n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 12n)
        case 13n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 13n)
        case 14n:
          add_succ(Nat.mul(horner(16n, t, 0n), 16n), 14n)
        case 15n:
          %Equal.sym(Nat, Nat.add(Nat.mul(horner(16n, N.hex_inc(t), 0n), 16n), 0n), Nat.mul(horner(16n, N.hex_inc(t), 0n), 16n), add_zero(Nat.mul(horner(16n, N.hex_inc(t), 0n), 16n))) : {_ == 1n+Nat.add(Nat.mul(horner(16n, t, 0n), 16n), 15n) : Nat}
          %Equal.sym(Nat, horner(16n, N.hex_inc(t), 0n), 1n+horner(16n, t, 0n), hex_inc_val(t, e)) : {Nat.mul(_, 16n) == 1n+Nat.add(Nat.mul(horner(16n, t, 0n), 16n), 15n) : Nat}
          %add_comm(Nat.mul(horner(16n, t, 0n), 16n), 15n) : {1n+_ == 1n+Nat.add(Nat.mul(horner(16n, t, 0n), 16n), 15n) : Nat}
          {==}
        case 16n+k:
          Empty.absurd({horner(16n, N.hex_inc(Con{16n+k, t}), 0n) == 1n+horner(16n, Con{16n+k, t}, 0n) : Nat}, false_true(e))

def hex_count_ok(n: Nat, +ds: NL(), e: {digits_ok(15n, ds) == True{} : Bool}) -> {digits_ok(15n, N.hex_count(n, ds)) == True{} : Bool}:
  match n:
    case 0n:
      e
    case 1n+p:
      hex_count_ok(p, N.hex_inc(ds), hex_inc_ok(ds, e))

def hex_count_con(n: Nat, +ds: NL(), e: {is_con(ds) == True{} : Bool}) -> {is_con(N.hex_count(n, ds)) == True{} : Bool}:
  match n:
    case 0n:
      e
    case 1n+p:
      hex_count_con(p, N.hex_inc(ds), hex_inc_con(ds))

# n increments add n to the value.
def hex_count_val(n: Nat, +ds: NL(), +e: {digits_ok(15n, ds) == True{} : Bool}) -> {horner(16n, N.hex_count(n, ds), 0n) == Nat.add(n, horner(16n, ds, 0n)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, horner(16n, N.hex_count(p, N.hex_inc(ds)), 0n), Nat.add(p, horner(16n, N.hex_inc(ds), 0n)), hex_count_val(p, N.hex_inc(ds), hex_inc_ok(ds, e))) : {_ == 1n+Nat.add(p, horner(16n, ds, 0n)) : Nat}
      %Equal.sym(Nat, horner(16n, N.hex_inc(ds), 0n), 1n+horner(16n, ds, 0n), hex_inc_val(ds, e)) : {Nat.add(p, _) == 1n+Nat.add(p, horner(16n, ds, 0n)) : Nat}
      add_succ(p, horner(16n, ds, 0n))

# Reading the text of ds from Some{a} reaches Some{horner(ds, a)} when that
# is at most LIMIT (and so is every accumulator on the way).
def hex_fold(ds: NL(), +acc: String, +a: Nat, +ok: {digits_ok(15n, ds) == True{} : Bool}, lim: {Nat.is_le(horner(16n, ds, a), N.LIMIT()) == True{} : Bool})
  -> {N.hex_read.go(N.digits_text(ds, acc), Some{a}) == N.hex_read.go(acc, Some{horner(16n, ds, a)}) : MN()}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      okd = and_l(Nat.is_le(d, 15n), digits_ok(15n, t), ok)
      okt = and_r(Nat.is_le(d, 15n), digits_ok(15n, t), ok)
      +limt = le_trans(horner(16n, t, a), Nat.add(Nat.mul(horner(16n, t, a), 16n), d), N.LIMIT(), le_push(horner(16n, t, a), 15n, d), lim)
      %Equal.sym(MN(), N.hex_read.go(N.digits_text(t, SCon{N.digit_char(d), acc}), Some{a}), N.hex_read.go(SCon{N.digit_char(d), acc}, Some{horner(16n, t, a)}), hex_fold(t, SCon{N.digit_char(d), acc}, a, okt, limt)) : {_ == N.hex_read.go(acc, Some{Nat.add(Nat.mul(horner(16n, t, a), 16n), d)}) : MN()}
      %Equal.sym(MN(), N.hex_value(B.char_class(N.digit_char(d))), Some{d}, hex_char(d, okd)) : {N.hex_read.go(acc, N.read.step(Some{horner(16n, t, a)}, 16n, _)) == N.hex_read.go(acc, Some{Nat.add(Nat.mul(horner(16n, t, a), 16n), d)}) : MN()}
      %Equal.sym(Bool, Nat.is_le(horner(16n, t, a), N.LIMIT()), True{}, limt) : {N.hex_read.go(acc, Some{N.push.pick(_, horner(16n, t, a), 16n, d)}) == N.hex_read.go(acc, Some{Nat.add(Nat.mul(horner(16n, t, a), 16n), d)}) : MN()}
      {==}

# The digits of n have value n.
def hex_digits_val(+n: Nat) -> {horner(16n, N.hex_count(n, [0n]), 0n) == n : Nat}:
  Equal.trans(Nat, horner(16n, N.hex_count(n, [0n]), 0n), Nat.add(n, 0n), n, hex_count_val(n, [0n], {==}), add_zero(n))

def hex_digits_lim(+n: Nat, e: {Nat.is_le(n, N.LIMIT()) == True{} : Bool}) -> {Nat.is_le(horner(16n, N.hex_count(n, [0n]), 0n), N.LIMIT()) == True{} : Bool}:
  %Equal.sym(Nat, horner(16n, N.hex_count(n, [0n]), 0n), n, hex_digits_val(n)) : {Nat.is_le(_, N.LIMIT()) == True{} : Bool}
  e

def Laws.hex_roundtrip(n, e0):
  +e = e0
  %Equal.sym(MN(), N.hex_read(N.digits_text(N.hex_count(n, [0n]), SNil{})), N.bound(N.hex_read.go(N.digits_text(N.hex_count(n, [0n]), SNil{}), Some{0n})), hex_read_con(N.hex_count(n, [0n]), hex_count_con(n, [0n], {==}))) : {_ == Some{n} : MN()}
  %Equal.sym(MN(), N.hex_read.go(N.digits_text(N.hex_count(n, [0n]), SNil{}), Some{0n}), N.hex_read.go(SNil{}, Some{horner(16n, N.hex_count(n, [0n]), 0n)}), hex_fold(N.hex_count(n, [0n]), SNil{}, 0n, hex_count_ok(n, [0n], {==}), hex_digits_lim(n, e))) : {N.bound(_) == Some{n} : MN()}
  %Equal.sym(Nat, horner(16n, N.hex_count(n, [0n]), 0n), n, hex_digits_val(n)) : {N.bound(Some{_}) == Some{n} : MN()}
  %Equal.sym(Bool, Nat.is_le(n, N.LIMIT()), True{}, e) : {N.bound.pick(_, n) == Some{n} : MN()}
  {==}
