# Law 18: header lookup ignores the case of the name.
#
# get(name, hs) is get.go(lower(name), hs, None{}), so the law is
# get.go(lower(lower(n)), hs, None{}) == get.go(lower(n), hs, None{}): it
# follows from lower(lower(n)) == lower(n), whatever the header list.
#   - lower.go(s, acc) == String.reverse.go(acc, lower.spec(s)) (the loop's
#     .spec equation), so lower == lower.spec;
#   - lower_char is idempotent: lower_char(c) tests
#     letter(c), letter(c + 32), not letter((c + 32) + 32); when it fires the
#     result is c + 32, whose own test asks letter((c + 32) + 32) first-but-one,
#     the very term found not a letter, so the second lowering is a no-op;
#   - so lower.spec, and hence lower, is idempotent.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/headers.bend as H

# lower_char
# ----------

# Whether the char with code x is an ASCII letter of either case.
def hl_letter(+x: U32) -> Bool:
  H.is_letter(B.class(x))

# lower_char(Chr{x}) as a pick on the three letter tests, named a, b, c.
def lower_char_pick(+x: U32, -a: Bool, -b: Bool, -c: Bool,
  ea: {a == H.is_letter(B.class(x)) : Bool},
  eb: {b == H.is_letter(B.class(H.up32(x))) : Bool},
  ec: {c == H.is_letter(B.class(H.up32(H.up32(x)))) : Bool})
  -> {H.lower_char(Chr{x}) == H.lower_char.pick(a && b && Bool.not(c), Chr{x}) : Char}:
  %ea : {H.lower_char.pick(_ && H.is_letter(B.class(H.up32(x))) && Bool.not(H.is_letter(B.class(H.up32(H.up32(x))))), Chr{x}) == H.lower_char.pick(a && b && Bool.not(c), Chr{x}) : Char}
  %eb : {H.lower_char.pick(a && _ && Bool.not(H.is_letter(B.class(H.up32(H.up32(x))))), Chr{x}) == H.lower_char.pick(a && b && Bool.not(c), Chr{x}) : Char}
  %ec : {H.lower_char.pick(a && b && Bool.not(_), Chr{x}) == H.lower_char.pick(a && b && Bool.not(c), Chr{x}) : Char}
  {==}

# Idempotence for one code, by cases on its three letter tests.
def lower_char_idem_at(+x: U32, a: Bool, b: Bool, c: Bool,
  +ea: {a == H.is_letter(B.class(x)) : Bool},
  +eb: {b == H.is_letter(B.class(H.up32(x))) : Bool},
  +ec: {c == H.is_letter(B.class(H.up32(H.up32(x)))) : Bool})
  -> {H.lower_char(H.lower_char(Chr{x})) == H.lower_char(Chr{x}) : Char}:
  match a:
    case False{}:
      %Equal.sym(Char, H.lower_char(Chr{x}), Chr{x}, lower_char_pick(x, False{}, b, c, ea, eb, ec)) : {H.lower_char(_) == _ : Char}
      lower_char_pick(x, False{}, b, c, ea, eb, ec)
    case True{}:
      match b:
        case False{}:
          %Equal.sym(Char, H.lower_char(Chr{x}), Chr{x}, lower_char_pick(x, True{}, False{}, c, ea, eb, ec)) : {H.lower_char(_) == _ : Char}
          lower_char_pick(x, True{}, False{}, c, ea, eb, ec)
        case True{}:
          match c:
            case True{}:
              %Equal.sym(Char, H.lower_char(Chr{x}), Chr{x}, lower_char_pick(x, True{}, True{}, True{}, ea, eb, ec)) : {H.lower_char(_) == _ : Char}
              lower_char_pick(x, True{}, True{}, True{}, ea, eb, ec)
            case False{}:
              %Equal.sym(Char, H.lower_char(Chr{x}), Chr{H.up32(x)}, lower_char_pick(x, True{}, True{}, False{}, ea, eb, ec)) : {H.lower_char(_) == _ : Char}
              lower_char_pick(H.up32(x), True{}, False{}, hl_letter(H.up32(H.up32(H.up32(x)))), eb, ec, {==})

def lower_char_idem(c: Char) -> {H.lower_char(H.lower_char(c)) == H.lower_char(c) : Char}:
  match c:
    case Chr{+x}:
      lower_char_idem_at(x, hl_letter(x), hl_letter(H.up32(x)), hl_letter(H.up32(H.up32(x))), {==}, {==}, {==})

# lower
# -----

# The loop's .spec equation (headers.bend header).
def lower_go_spec(s: String, -acc: String) -> {H.lower.go(s, acc) == String.reverse.go(acc, H.lower.spec(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      lower_go_spec(t, SCon{H.lower_char(c), acc})

def lower_eq_spec(s: String) -> {H.lower(s) == H.lower.spec(s) : String}:
  lower_go_spec(s, SNil{})

def lower_spec_idem(s: String) -> {H.lower.spec(H.lower.spec(s)) == H.lower.spec(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %lower_char_idem(c) : {SCon{H.lower_char(H.lower_char(c)), H.lower.spec(H.lower.spec(t))} == SCon{_, H.lower.spec(t)} : String}
      %lower_spec_idem(t) : {SCon{H.lower_char(H.lower_char(c)), H.lower.spec(H.lower.spec(t))} == SCon{H.lower_char(H.lower_char(c)), _} : String}
      {==}

# lower(lower(s)) == lower(s).
def lower_idem(+s: String) -> {H.lower(H.lower(s)) == H.lower(s) : String}:
  %Equal.sym(String, H.lower(s), H.lower.spec(s), lower_eq_spec(s)) : {H.lower(_) == _ : String}
  %Equal.sym(String, H.lower(H.lower.spec(s)), H.lower.spec(H.lower.spec(s)), lower_eq_spec(H.lower.spec(s))) : {_ == H.lower.spec(s) : String}
  lower_spec_idem(s)

# Law 18
# ------

def Laws.header_lookup_case(n, hs):
  %Equal.sym(String, H.lower(H.lower(n)), H.lower(n), lower_idem(n)) : {H.get.go(_, hs, None{}) == H.get(n, hs) : Maybe<&2, String>}
  {==}
