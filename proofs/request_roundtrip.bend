# Law 7 (request_roundtrip): SR.decode_request reads back what E emits.
#
# The plan:
#   1. request_bytes(r) is from_ascii.spec(head) ++ body (bytes.bend's loop
#      equation), and header_lines is header_lines.spec (encode.bend's).
#   2. The head is reshaped (String.append associativity) into its lines:
#        line0 ++ "\r\n" ++ (l1 ++ "\r\n" ++ (... ++ "\r\n" ++ "\r\n"))
#      with line0 = method SP target SP "HTTP/1.1" and li = name ": " value.
#   3. A line with no CR char, read in mode Mid (or Start, when it is
#      nonempty), conses its chars onto the line that new_line opens after
#      its CRLF: head_lines gives Some{Lines{line0 <> texts(headers), body}}.
#   4. The request line splits at SP twice (method and target hold no SP) and
#      each field line at its first ':' (a header name holds none).
#   5. request_ok gives every fact the steps need: method_ok (a token or a
#      fixed name), U.ok (host chars, target chars), H.headers_ok (token
#      names, field-char values); Host, Content-Length (N.show's digits) and
#      Connection are checked by computation.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/url.bend as U
import ../src/encode.bend as E
import ../src/spec_request.bend as SR

def rr_ML() -> Data:
  Maybe<&2, SR.Lines>

def rr_MS() -> Data:
  Maybe<&2, SR.Split>

def rr_MH() -> Data:
  Maybe<&2, List<&2, M.Header>>

def rr_MR() -> Data:
  Maybe<&2, SR.ParsedRequest>

# Bool facts
# ----------

def rr_bdisc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def rr_false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : rr_bdisc(_)
  Unit{}

# P when b holds (Unit otherwise): a lemma true only for some classes.
def rr_when(b: Bool, P: Type) -> Type:
  match b:
    case True{}:
      P
    case False{}:
      Unit

def rr_use(+b: Bool, -P: Type, w: rr_when(b, P), e: {b == True{} : Bool}) -> P:
  match b:
    case True{}:
      w
    case False{}:
      Empty.absurd(P, rr_false_true(e))

def rr_and_l(+a: Bool, +b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))

def rr_and_r(+a: Bool, +b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, rr_false_true(e))

def rr_and_intro(+a: Bool, +b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool})
  -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(ea))

def rr_and_true(+a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def rr_and_assoc(+a: Bool, +b: Bool, +c: Bool)
  -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Strings
# -------

def rr_str_assoc(+a: String, +b: String, +c: String)
  -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      %rr_str_assoc(t, b, c) : {SCon{x, String.append(String.append(t, b), c)} == SCon{x, _} : String}
      {==}

def rr_str_nil(+a: String) -> {String.append(a, SNil{}) == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      %rr_str_nil(t) : {SCon{x, String.append(t, SNil{})} == SCon{x, _} : String}
      {==}

# A field line's text, then CRLF and the rest (oriented to rewrite the old
# form into the new).
def rr_hdr_reshape0(+n: String, +v: String, +z: String)
  -> {String.append(String.append(n, String.append(": ", v)), String.append("\r\n", z))
      == String.append(String.append(n, String.append(": ", String.append(v, "\r\n"))), z) : String}:
  match n:
    case SNil{}:
      %rr_str_assoc(v, "\r\n", z) : {SCon{':', SCon{' ', _}} == SCon{':', SCon{' ', String.append(String.append(v, "\r\n"), z)}} : String}
      {==}
    case SCon{+x, +t}:
      %rr_hdr_reshape0(t, v, z) : {SCon{x, String.append(String.append(t, String.append(": ", v)), String.append("\r\n", z))} == SCon{x, _} : String}
      {==}

def rr_hdr_reshape(+n: String, +v: String, +hs: String)
  -> {String.append(String.append(n, String.append(": ", v)), String.append("\r\n", String.append(hs, "\r\n")))
      == String.append(String.append(E.header_line(M.Header{n, v}), hs), "\r\n") : String}:
  Equal.trans(String,
    String.append(String.append(n, String.append(": ", v)), String.append("\r\n", String.append(hs, "\r\n"))),
    String.append(E.header_line(M.Header{n, v}), String.append(hs, "\r\n")),
    String.append(String.append(E.header_line(M.Header{n, v}), hs), "\r\n"),
    rr_hdr_reshape0(n, v, String.append(hs, "\r\n")),
    Equal.sym(String,
      String.append(String.append(E.header_line(M.Header{n, v}), hs), "\r\n"),
      String.append(E.header_line(M.Header{n, v}), String.append(hs, "\r\n")),
      rr_str_assoc(E.header_line(M.Header{n, v}), hs, "\r\n")))

def rr_line0(mn: String, t: String) -> String:
  String.append(mn, String.append(" ", String.append(t, " HTTP/1.1")))

# The request line, then CRLF and the rest.
def rr_head_reshape(+a: String, +t: String, +z: String)
  -> {String.append(String.append(a, String.append(" ", String.append(t, " HTTP/1.1"))), String.append("\r\n", z))
      == String.append(a, String.append(" ", String.append(t, String.append(" HTTP/1.1\r\n", z)))) : String}:
  match a:
    case SNil{}:
      %rr_str_assoc(t, " HTTP/1.1", String.append("\r\n", z)) : {SCon{' ', String.append(String.append(t, " HTTP/1.1"), String.append("\r\n", z))} == SCon{' ', _} : String}
      {==}
    case SCon{+x, +r}:
      %rr_head_reshape(r, t, z) : {SCon{x, String.append(String.append(r, String.append(" ", String.append(t, " HTTP/1.1"))), String.append("\r\n", z))} == SCon{x, _} : String}
      {==}

# Char classes
# ------------

# Not CR: may sit inside a head line.
def rr_lc(k: B.Class) -> Bool:
  match k:
    case B.Cr{}:
      False{}
    case _:
      True{}

# Not CR, not SP: may sit in the method or the target.
def rr_rc(k: B.Class) -> Bool:
  match k:
    case B.Cr{}:
      False{}
    case B.Sp{}:
      False{}
    case _:
      True{}

# Not CR, not ':': may sit in a header name.
def rr_nc(k: B.Class) -> Bool:
  match k:
    case B.Cr{}:
      False{}
    case B.Colon{}:
      False{}
    case _:
      True{}

def rr_all_lc(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(rr_lc(B.char_class(c)), rr_all_lc(t))

def rr_all_rc(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(rr_rc(B.char_class(c)), rr_all_rc(t))

def rr_all_nc(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(rr_nc(B.char_class(c)), rr_all_nc(t))

def rr_nonnil(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      True{}

def rr_rc_lc(+k: B.Class, e: {rr_rc(k) == True{} : Bool}) -> {rr_lc(k) == True{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_nc_lc(+k: B.Class, e: {rr_nc(k) == True{} : Bool}) -> {rr_lc(k) == True{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_tchar_rc(+k: B.Class, e: {B.Class.is_tchar(k) == True{} : Bool}) -> {rr_rc(k) == True{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_tchar_nc(+k: B.Class, e: {B.Class.is_tchar(k) == True{} : Bool}) -> {rr_nc(k) == True{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_field_lc(+k: B.Class, e: {B.Class.is_field_char(k) == True{} : Bool}) -> {rr_lc(k) == True{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_host_lc(+k: B.Class, +c: Char, e: {U.UClass.is_host(U.uclass.of(k, c)) == True{} : Bool})
  -> {rr_lc(k) == True{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_slash_rc(+k: B.Class, +c: Char, e: {U.UClass.is_slash(U.uclass.of(k, c)) == True{} : Bool})
  -> {rr_rc(k) == True{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_target_rc(+k: B.Class, +c: Char, e: {U.UClass.is_target(U.uclass.of(k, c)) == True{} : Bool})
  -> {rr_rc(k) == True{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Empty.absurd({False{} == True{} : Bool}, rr_false_true(e))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

# Every digit char (and the '?' past 15) may sit in a head line.
def rr_digit_lc(+d: Nat) -> {rr_lc(B.char_class(N.digit_char(d))) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+d1:
      match d1:
        case 0n:
          {==}
        case 1n+d2:
          match d2:
            case 0n:
              {==}
            case 1n+d3:
              match d3:
                case 0n:
                  {==}
                case 1n+d4:
                  match d4:
                    case 0n:
                      {==}
                    case 1n+d5:
                      match d5:
                        case 0n:
                          {==}
                        case 1n+d6:
                          match d6:
                            case 0n:
                              {==}
                            case 1n+d7:
                              match d7:
                                case 0n:
                                  {==}
                                case 1n+d8:
                                  match d8:
                                    case 0n:
                                      {==}
                                    case 1n+d9:
                                      match d9:
                                        case 0n:
                                          {==}
                                        case 1n+d10:
                                          match d10:
                                            case 0n:
                                              {==}
                                            case 1n+d11:
                                              match d11:
                                                case 0n:
                                                  {==}
                                                case 1n+d12:
                                                  match d12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+d13:
                                                      match d13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+d14:
                                                          match d14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+d15:
                                                              match d15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+d16:
                                                                  {==}

# head_lines steps on a char that is not CR (oriented new == old)
def rr_step_mid_w(+k: B.Class, +h: U32, +tl: List<&2, U32>)
  -> rr_when(rr_lc(k), {SR.cons_line(h, SR.head_lines.go(tl, SR.Mid{}))
       == SR.act(SR.Mid{}, k, h, SR.head_lines.go(tl, SR.next(SR.Mid{}, k))) : rr_ML()}):
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Unit{}
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_step_mid(+k: B.Class, +h: U32, +tl: List<&2, U32>, +e: {rr_lc(k) == True{} : Bool})
  -> {SR.cons_line(h, SR.head_lines.go(tl, SR.Mid{}))
       == SR.act(SR.Mid{}, k, h, SR.head_lines.go(tl, SR.next(SR.Mid{}, k))) : rr_ML()}:
  rr_use(rr_lc(k), {SR.cons_line(h, SR.head_lines.go(tl, SR.Mid{}))
       == SR.act(SR.Mid{}, k, h, SR.head_lines.go(tl, SR.next(SR.Mid{}, k))) : rr_ML()},
    rr_step_mid_w(k, h, tl), e)

def rr_step_start_w(+k: B.Class, +h: U32, +tl: List<&2, U32>)
  -> rr_when(rr_lc(k), {SR.cons_line(h, SR.head_lines.go(tl, SR.Mid{}))
       == SR.act(SR.Start{}, k, h, SR.head_lines.go(tl, SR.next(SR.Start{}, k))) : rr_ML()}):
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Unit{}
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_step_start(+k: B.Class, +h: U32, +tl: List<&2, U32>, +e: {rr_lc(k) == True{} : Bool})
  -> {SR.cons_line(h, SR.head_lines.go(tl, SR.Mid{}))
       == SR.act(SR.Start{}, k, h, SR.head_lines.go(tl, SR.next(SR.Start{}, k))) : rr_ML()}:
  rr_use(rr_lc(k), {SR.cons_line(h, SR.head_lines.go(tl, SR.Mid{}))
       == SR.act(SR.Start{}, k, h, SR.head_lines.go(tl, SR.next(SR.Start{}, k))) : rr_ML()},
    rr_step_start_w(k, h, tl), e)

# split_sp / split_colon step past a char that is not the stop char
def rr_pick_sp_w(+k: B.Class, +c: Char, +t: String, +r: rr_MS())
  -> rr_when(rr_rc(k), {SR.split.con(c, r) == SR.split_sp.pick(k, c, t, r) : rr_MS()}):
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      Unit{}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Unit{}
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_pick_sp(+k: B.Class, +c: Char, +t: String, +r: rr_MS(), +e: {rr_rc(k) == True{} : Bool})
  -> {SR.split.con(c, r) == SR.split_sp.pick(k, c, t, r) : rr_MS()}:
  rr_use(rr_rc(k), {SR.split.con(c, r) == SR.split_sp.pick(k, c, t, r) : rr_MS()},
    rr_pick_sp_w(k, c, t, r), e)

def rr_pick_colon_w(+k: B.Class, +c: Char, +t: String, +r: rr_MS())
  -> rr_when(rr_nc(k), {SR.split.con(c, r) == SR.split_colon.pick(k, c, t, r) : rr_MS()}):
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      Unit{}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      Unit{}
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def rr_pick_colon(+k: B.Class, +c: Char, +t: String, +r: rr_MS(), +e: {rr_nc(k) == True{} : Bool})
  -> {SR.split.con(c, r) == SR.split_colon.pick(k, c, t, r) : rr_MS()}:
  rr_use(rr_nc(k), {SR.split.con(c, r) == SR.split_colon.pick(k, c, t, r) : rr_MS()},
    rr_pick_colon_w(k, c, t, r), e)

# String predicates
# -----------------

def rr_rc_lc_s(+s: String, +e: {rr_all_rc(s) == True{} : Bool}) -> {rr_all_lc(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_and_intro(rr_lc(B.char_class(c)), rr_all_lc(t),
        rr_rc_lc(B.char_class(c), rr_and_l(rr_rc(B.char_class(c)), rr_all_rc(t), e)),
        rr_rc_lc_s(t, rr_and_r(rr_rc(B.char_class(c)), rr_all_rc(t), e)))

def rr_nc_lc_s(+s: String, +e: {rr_all_nc(s) == True{} : Bool}) -> {rr_all_lc(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_and_intro(rr_lc(B.char_class(c)), rr_all_lc(t),
        rr_nc_lc(B.char_class(c), rr_and_l(rr_nc(B.char_class(c)), rr_all_nc(t), e)),
        rr_nc_lc_s(t, rr_and_r(rr_nc(B.char_class(c)), rr_all_nc(t), e)))

def rr_all_lc_app(+a: String, +b: String, +ea: {rr_all_lc(a) == True{} : Bool}, +eb: {rr_all_lc(b) == True{} : Bool})
  -> {rr_all_lc(String.append(a, b)) == True{} : Bool}:
  match a:
    case SNil{}:
      eb
    case SCon{+c, +t}:
      rr_and_intro(rr_lc(B.char_class(c)), rr_all_lc(String.append(t, b)),
        rr_and_l(rr_lc(B.char_class(c)), rr_all_lc(t), ea),
        rr_all_lc_app(t, b, rr_and_r(rr_lc(B.char_class(c)), rr_all_lc(t), ea), eb))

def rr_nonnil_app(+a: String, +b: String, +e: {rr_nonnil(b) == True{} : Bool})
  -> {rr_nonnil(String.append(a, b)) == True{} : Bool}:
  match a:
    case SNil{}:
      e
    case SCon{+c, +t}:
      {==}

# N.show writes digit chars only.
def rr_dt_lc(+ds: List<&2, Nat>, +acc: String, +e: {rr_all_lc(acc) == True{} : Bool})
  -> {rr_all_lc(N.digits_text(ds, acc)) == True{} : Bool}:
  match ds:
    case Nil{}:
      e
    case Con{+d, +t}:
      rr_dt_lc(t, SCon{N.digit_char(d), acc},
        rr_and_intro(rr_lc(B.char_class(N.digit_char(d))), rr_all_lc(acc), rr_digit_lc(d), e))

def rr_show_lc(+n: Nat) -> {rr_all_lc(N.show(n)) == True{} : Bool}:
  rr_dt_lc(N.dec_digits(n), SNil{}, {==})

# Loop equations (bytes.bend, headers.bend, encode.bend)
# -------------------------------------------------------

def rr_tchar_go(+s: String, +ok: Bool)
  -> {H.all_tchar.go(s, ok) == Bool.and(ok, H.all_tchar.spec(s)) : Bool}:
  match s:
    case SNil{}:
      Equal.sym(Bool, Bool.and(ok, True{}), ok, rr_and_true(ok))
    case SCon{+c, +t}:
      Equal.trans(Bool,
        H.all_tchar.go(t, Bool.and(ok, B.Class.is_tchar(B.char_class(c)))),
        Bool.and(Bool.and(ok, B.Class.is_tchar(B.char_class(c))), H.all_tchar.spec(t)),
        Bool.and(ok, Bool.and(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t))),
        rr_tchar_go(t, Bool.and(ok, B.Class.is_tchar(B.char_class(c)))),
        rr_and_assoc(ok, B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t)))

def rr_field_go(+s: String, +ok: Bool)
  -> {H.all_field_char.go(s, ok) == Bool.and(ok, H.all_field_char.spec(s)) : Bool}:
  match s:
    case SNil{}:
      Equal.sym(Bool, Bool.and(ok, True{}), ok, rr_and_true(ok))
    case SCon{+c, +t}:
      Equal.trans(Bool,
        H.all_field_char.go(t, Bool.and(ok, B.Class.is_field_char(B.char_class(c)))),
        Bool.and(Bool.and(ok, B.Class.is_field_char(B.char_class(c))), H.all_field_char.spec(t)),
        Bool.and(ok, Bool.and(B.Class.is_field_char(B.char_class(c)), H.all_field_char.spec(t))),
        rr_field_go(t, Bool.and(ok, B.Class.is_field_char(B.char_class(c)))),
        rr_and_assoc(ok, B.Class.is_field_char(B.char_class(c)), H.all_field_char.spec(t)))

def rr_hok_go(+hs: List<&2, M.Header>, +ok: Bool)
  -> {H.headers_ok.go(hs, ok) == Bool.and(ok, H.headers_ok.spec(hs)) : Bool}:
  match hs:
    case Nil{}:
      Equal.sym(Bool, Bool.and(ok, True{}), ok, rr_and_true(ok))
    case Con{+h, +t}:
      Equal.trans(Bool,
        H.headers_ok.go(t, Bool.and(ok, H.header_ok(h))),
        Bool.and(Bool.and(ok, H.header_ok(h)), H.headers_ok.spec(t)),
        Bool.and(ok, Bool.and(H.header_ok(h), H.headers_ok.spec(t))),
        rr_hok_go(t, Bool.and(ok, H.header_ok(h))),
        rr_and_assoc(ok, H.header_ok(h), H.headers_ok.spec(t)))

# rev(from_ascii.rev(s, acc), ys) == rev(acc, from_ascii.spec(s) ++ ys)
def rr_from_ascii_rev(+s: String, +acc: List<&2, U32>, +ys: List<&2, U32>)
  -> {B.rev(U32, B.from_ascii.rev(s, acc), ys)
      == B.rev(U32, acc, List.append(&2, U32, B.from_ascii.spec(s), ys)) : List<&2, U32>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_from_ascii_rev(t, Char.to_u32(c) <> acc, ys)

# from_ascii.spec(s) ++ ys == from_ascii_onto(s, ys)  (new == old)
def rr_onto(+s: String, +ys: List<&2, U32>)
  -> {List.append(&2, U32, B.from_ascii.spec(s), ys) == B.from_ascii_onto(s, ys) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.from_ascii_onto(s, ys), List.append(&2, U32, B.from_ascii.spec(s), ys),
    rr_from_ascii_rev(s, Nil{}, ys))

# rev(rev(hs, acc), ys) == rev(acc, hs ++ ys)
def rr_rev_rev(+hs: List<&2, M.Header>, +acc: List<&2, M.Header>, +ys: List<&2, M.Header>)
  -> {B.rev(M.Header, B.rev(M.Header, hs, acc), ys) == B.rev(M.Header, acc, List.append(&2, M.Header, hs, ys)) : List<&2, M.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      rr_rev_rev(t, h <> acc, ys)

# lines_onto(rev(hs, acc), s) == lines_onto(acc, header_lines.spec(hs) ++ s)
def rr_lines_onto(+hs: List<&2, M.Header>, +acc: List<&2, M.Header>, +s: String)
  -> {E.lines_onto(B.rev(M.Header, hs, acc), s)
      == E.lines_onto(acc, String.append(E.header_lines.spec(hs), s)) : String}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(String,
        String.append(String.append(E.header_line(h), E.header_lines.spec(t)), s),
        String.append(E.header_line(h), String.append(E.header_lines.spec(t), s)),
        rr_str_assoc(E.header_line(h), E.header_lines.spec(t), s)) : {E.lines_onto(B.rev(M.Header, t, h <> acc), s) == E.lines_onto(acc, _) : String}
      rr_lines_onto(t, h <> acc, s)

# header_lines.spec(hs) == header_lines(hs)  (new == old)
def rr_hl_spec(+hs: List<&2, M.Header>) -> {E.header_lines.spec(hs) == E.header_lines(hs) : String}:
  Equal.sym(String, E.header_lines(hs), E.header_lines.spec(hs),
    Equal.trans(String, E.header_lines(hs), String.append(E.header_lines.spec(hs), SNil{}), E.header_lines.spec(hs),
      rr_lines_onto(hs, Nil{}, SNil{}), rr_str_nil(E.header_lines.spec(hs))))

# Facts from request_ok
# ---------------------

def rr_token_spec(+n: String, +e: {H.is_token(n) == True{} : Bool}) -> {H.all_tchar.spec(n) == True{} : Bool}:
  match n:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(Bool, H.all_tchar.spec(SCon{c, t}), H.all_tchar.go(t, B.Class.is_tchar(B.char_class(c))), True{},
        Equal.sym(Bool, H.all_tchar.go(t, B.Class.is_tchar(B.char_class(c))),
          Bool.and(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t)),
          rr_tchar_go(t, B.Class.is_tchar(B.char_class(c)))),
        e)

def rr_tchar_spec_rc(+s: String, +e: {H.all_tchar.spec(s) == True{} : Bool}) -> {rr_all_rc(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_and_intro(rr_rc(B.char_class(c)), rr_all_rc(t),
        rr_tchar_rc(B.char_class(c), rr_and_l(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), e)),
        rr_tchar_spec_rc(t, rr_and_r(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), e)))

def rr_tchar_spec_nc(+s: String, +e: {H.all_tchar.spec(s) == True{} : Bool}) -> {rr_all_nc(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_and_intro(rr_nc(B.char_class(c)), rr_all_nc(t),
        rr_tchar_nc(B.char_class(c), rr_and_l(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), e)),
        rr_tchar_spec_nc(t, rr_and_r(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), e)))

def rr_field_spec_lc(+s: String, +e: {H.all_field_char.spec(s) == True{} : Bool}) -> {rr_all_lc(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_and_intro(rr_lc(B.char_class(c)), rr_all_lc(t),
        rr_field_lc(B.char_class(c), rr_and_l(B.Class.is_field_char(B.char_class(c)), H.all_field_char.spec(t), e)),
        rr_field_spec_lc(t, rr_and_r(B.Class.is_field_char(B.char_class(c)), H.all_field_char.spec(t), e)))

def rr_host_all_lc(+s: String, +e: {U.all_host(s) == True{} : Bool}) -> {rr_all_lc(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_and_intro(rr_lc(B.char_class(c)), rr_all_lc(t),
        rr_host_lc(B.char_class(c), c, rr_and_l(U.UClass.is_host(U.uclass(c)), U.all_host(t), e)),
        rr_host_all_lc(t, rr_and_r(U.UClass.is_host(U.uclass(c)), U.all_host(t), e)))

def rr_host_chars_lc(+s: String, +e: {U.host_chars(s) == True{} : Bool}) -> {rr_all_lc(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_and_intro(rr_lc(B.char_class(c)), rr_all_lc(t),
        rr_host_lc(B.char_class(c), c, rr_and_l(U.UClass.is_host(U.uclass(c)), U.all_host(t), e)),
        rr_host_all_lc(t, rr_and_r(U.UClass.is_host(U.uclass(c)), U.all_host(t), e)))

def rr_target_all_rc(+s: String, +e: {U.all_target(s) == True{} : Bool}) -> {rr_all_rc(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_and_intro(rr_rc(B.char_class(c)), rr_all_rc(t),
        rr_target_rc(B.char_class(c), c, rr_and_l(U.UClass.is_target(U.uclass(c)), U.all_target(t), e)),
        rr_target_all_rc(t, rr_and_r(U.UClass.is_target(U.uclass(c)), U.all_target(t), e)))

def rr_target_ok_rc(+s: String, +e: {U.target_ok(s) == True{} : Bool}) -> {rr_all_rc(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      rr_and_intro(rr_rc(B.char_class(c)), rr_all_rc(t),
        rr_slash_rc(B.char_class(c), c, rr_and_l(U.UClass.is_slash(U.uclass(c)), U.all_target(t), e)),
        rr_target_all_rc(t, rr_and_r(U.UClass.is_slash(U.uclass(c)), U.all_target(t), e)))

def rr_method_rc(+m: M.Method, +e: {E.method_ok(m) == True{} : Bool}) -> {rr_all_rc(E.method_name(m)) == True{} : Bool}:
  match m:
    case M.GET{}:
      {==}
    case M.HEAD{}:
      {==}
    case M.POST{}:
      {==}
    case M.PUT{}:
      {==}
    case M.DELETE{}:
      {==}
    case M.PATCH{}:
      {==}
    case M.OPTIONS{}:
      {==}
    case M.Other{+n}:
      rr_tchar_spec_rc(n, rr_token_spec(n, rr_and_l(H.is_token(n), E.is_other(E.method_of(n)), e)))

# Header lists whose lines head_lines and fields read back
# ---------------------------------------------------------

def rr_hdr_good(h: M.Header) -> Bool:
  match h:
    case M.Header{n, v}:
      Bool.and(rr_all_nc(n), rr_all_lc(v))

def rr_hdrs_good(hs: List<&2, M.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(rr_hdr_good(h), rr_hdrs_good(t))

def rr_header_ok_good(+h: M.Header, +e: {H.header_ok(h) == True{} : Bool}) -> {rr_hdr_good(h) == True{} : Bool}:
  match h:
    case M.Header{+n, +v}:
      +et = rr_and_l(H.is_token(n), H.is_value(v), e)
      +ev = rr_and_r(H.is_token(n), H.is_value(v), e)
      +ef = rr_and_l(H.all_field_char(v), H.first_not_ows(v),
        rr_and_l(Bool.and(H.all_field_char(v), H.first_not_ows(v)), H.last_not_ows(v), ev))
      +efs = Equal.trans(Bool, H.all_field_char.spec(v), H.all_field_char(v), True{},
        Equal.sym(Bool, H.all_field_char.go(v, True{}), Bool.and(True{}, H.all_field_char.spec(v)), rr_field_go(v, True{})),
        ef)
      rr_and_intro(rr_all_nc(n), rr_all_lc(v), rr_tchar_spec_nc(n, rr_token_spec(n, et)), rr_field_spec_lc(v, efs))

def rr_hok_good(+hs: List<&2, M.Header>, +e: {H.headers_ok.spec(hs) == True{} : Bool}) -> {rr_hdrs_good(hs) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      rr_and_intro(rr_hdr_good(h), rr_hdrs_good(t),
        rr_header_ok_good(h, rr_and_l(H.header_ok(h), H.headers_ok.spec(t), e)),
        rr_hok_good(t, rr_and_r(H.header_ok(h), H.headers_ok.spec(t), e)))

def rr_hdrs_app(+xs: List<&2, M.Header>, +ys: List<&2, M.Header>,
  +ex: {rr_hdrs_good(xs) == True{} : Bool}, +ey: {rr_hdrs_good(ys) == True{} : Bool})
  -> {rr_hdrs_good(List.append(&2, M.Header, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ey
    case Con{+h, +t}:
      rr_and_intro(rr_hdr_good(h), rr_hdrs_good(List.append(&2, M.Header, t, ys)),
        rr_and_l(rr_hdr_good(h), rr_hdrs_good(t), ex),
        rr_hdrs_app(t, ys, rr_and_r(rr_hdr_good(h), rr_hdrs_good(t), ex), ey))

def rr_tail_good(+w: Bool, +body: List<&2, U32>)
  -> {rr_hdrs_good(List.append(&2, M.Header, E.length_header.pick(w, body), [M.Header{"Connection", "close"}])) == True{} : Bool}:
  match w:
    case True{}:
      rr_and_intro(rr_hdr_good(M.Header{"Content-Length", N.show(E.length(body))}),
        rr_hdrs_good([M.Header{"Connection", "close"}]),
        rr_show_lc(E.length(body)), {==})
    case False{}:
      {==}

def rr_port_pick_lc(+b: Bool, +p: Nat) -> {rr_all_lc(U.port_text.pick(b, p)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      rr_show_lc(p)

def rr_rest_good(+m: M.Method, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  +e: {H.headers_ok.spec(hs) == True{} : Bool})
  -> {rr_hdrs_good(B.rev(M.Header, B.rev(M.Header, hs, Nil{}), E.tail_headers(m, body))) == True{} : Bool}:
  %Equal.sym(List<&2, M.Header>,
    B.rev(M.Header, B.rev(M.Header, hs, Nil{}), E.tail_headers(m, body)),
    List.append(&2, M.Header, hs, E.tail_headers(m, body)),
    rr_rev_rev(hs, Nil{}, E.tail_headers(m, body))) : {rr_hdrs_good(_) == True{} : Bool}
  rr_hdrs_app(hs, E.tail_headers(m, body), rr_hok_good(hs, e), rr_tail_good(E.wants_length(m, body), body))

def rr_hl_good(+m: M.Method, +s: M.Scheme, +h: String, +p: Nat, +t: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  +ehs: {H.headers_ok.spec(hs) == True{} : Bool}, +eh: {rr_all_lc(h) == True{} : Bool})
  -> {rr_hdrs_good(E.headers_of(m, M.Url{s, h, p, t}, hs, body)) == True{} : Bool}:
  rr_and_intro(rr_hdr_good(M.Header{"Host", U.host_header(M.Url{s, h, p, t})}),
    rr_hdrs_good(B.rev(M.Header, B.rev(M.Header, hs, Nil{}), E.tail_headers(m, body))),
    rr_all_lc_app(h, U.port_text(s, p), eh, rr_port_pick_lc(Nat.is_eq(p, U.default_port(s)), p)),
    rr_rest_good(m, hs, body, ehs))

# head_lines
# ----------

# The bytes of s, CRLF, w, then ys.
def rr_lb(s: String, w: String, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, B.from_ascii.spec(String.append(s, String.append("\r\n", w))), ys)

def rr_rest_bytes(w: String, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, B.from_ascii.spec(w), ys)

# A line with no CR, read inside a line, ends at its CRLF.
def rr_mid_line(+s: String, +w: String, +ys: List<&2, U32>, +ls: List<&2, String>, +body: List<&2, U32>,
  +ea: {rr_all_lc(s) == True{} : Bool},
  +eh: {SR.head_lines.go(rr_rest_bytes(w, ys), SR.Start{}) == Some{SR.Lines{ls, body}} : rr_ML()})
  -> {SR.head_lines.go(rr_lb(s, w, ys), SR.Mid{}) == Some{SR.Lines{Con{s, ls}, body}} : rr_ML()}:
  match s:
    case SNil{}:
      %eh : {SR.new_line(SR.head_lines.go(rr_rest_bytes(w, ys), SR.Start{})) == SR.new_line(_) : rr_ML()}
      {==}
    case SCon{+c, +t}:
      match c:
        case Chr{+x}:
          +ec = rr_and_l(rr_lc(B.class(x)), rr_all_lc(t), ea)
          +et = rr_and_r(rr_lc(B.class(x)), rr_all_lc(t), ea)
          %rr_step_mid(B.class(x), x, rr_lb(t, w, ys), ec) : {_ == Some{SR.Lines{Con{SCon{Chr{x}, t}, ls}, body}} : rr_ML()}
          %rr_mid_line(t, w, ys, ls, body, et, eh) : {SR.cons_line(x, SR.head_lines.go(rr_lb(t, w, ys), SR.Mid{})) == SR.cons_line(x, _) : rr_ML()}
          {==}

# A nonempty line with no CR, read from the start of a line.
def rr_start_line(+s: String, +w: String, +ys: List<&2, U32>, +ls: List<&2, String>, +body: List<&2, U32>,
  +ea: {rr_all_lc(s) == True{} : Bool}, +en: {rr_nonnil(s) == True{} : Bool},
  +eh: {SR.head_lines.go(rr_rest_bytes(w, ys), SR.Start{}) == Some{SR.Lines{ls, body}} : rr_ML()})
  -> {SR.head_lines.go(rr_lb(s, w, ys), SR.Start{}) == Some{SR.Lines{Con{s, ls}, body}} : rr_ML()}:
  match s:
    case SNil{}:
      Empty.absurd({SR.head_lines.go(rr_lb(SNil{}, w, ys), SR.Start{}) == Some{SR.Lines{Con{SNil{}, ls}, body}} : rr_ML()},
        rr_false_true(en))
    case SCon{+c, +t}:
      match c:
        case Chr{+x}:
          +ec = rr_and_l(rr_lc(B.class(x)), rr_all_lc(t), ea)
          +et = rr_and_r(rr_lc(B.class(x)), rr_all_lc(t), ea)
          %rr_step_start(B.class(x), x, rr_lb(t, w, ys), ec) : {_ == Some{SR.Lines{Con{SCon{Chr{x}, t}, ls}, body}} : rr_ML()}
          %rr_mid_line(t, w, ys, ls, body, et, eh) : {SR.cons_line(x, SR.head_lines.go(rr_lb(t, w, ys), SR.Mid{})) == SR.cons_line(x, _) : rr_ML()}
          {==}

def rr_text(h: M.Header) -> String:
  match h:
    case M.Header{n, v}:
      String.append(n, String.append(": ", v))

def rr_texts(hs: List<&2, M.Header>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{rr_text(h), rr_texts(t)}

# The field lines and the blank line: their texts, then the body.
def rr_hdr_lines(+hs: List<&2, M.Header>, +ys: List<&2, U32>, +e: {rr_hdrs_good(hs) == True{} : Bool})
  -> {SR.head_lines.go(rr_rest_bytes(String.append(E.header_lines.spec(hs), "\r\n"), ys), SR.Start{})
      == Some{SR.Lines{rr_texts(hs), ys}} : rr_ML()}:
  match hs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case Con{+y, +r}:
          {==}
    case Con{+h, +t}:
      match h:
        case M.Header{+n, +v}:
          +eg = rr_and_l(rr_hdr_good(M.Header{n, v}), rr_hdrs_good(t), e)
          +et = rr_and_r(rr_hdr_good(M.Header{n, v}), rr_hdrs_good(t), e)
          +en = rr_and_l(rr_all_nc(n), rr_all_lc(v), eg)
          +ev = rr_and_r(rr_all_nc(n), rr_all_lc(v), eg)
          %rr_hdr_reshape(n, v, E.header_lines.spec(t)) : {SR.head_lines.go(List.append(&2, U32, B.from_ascii.spec(_), ys), SR.Start{}) == Some{SR.Lines{Con{String.append(n, String.append(": ", v)), rr_texts(t)}, ys}} : rr_ML()}
          rr_start_line(String.append(n, String.append(": ", v)), String.append(E.header_lines.spec(t), "\r\n"), ys, rr_texts(t), ys,
            rr_all_lc_app(n, String.append(": ", v), rr_nc_lc_s(n, en), ev),
            rr_nonnil_app(n, String.append(": ", v), {==}),
            rr_hdr_lines(t, ys, et))

# Splitting
# ---------

def rr_split_sp(+a: String, +rest: String, +e: {rr_all_rc(a) == True{} : Bool})
  -> {SR.split_sp(String.append(a, SCon{' ', rest})) == Some{SR.Split{a, rest}} : rr_MS()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %rr_pick_sp(B.char_class(c), c, String.append(t, SCon{' ', rest}), SR.split_sp(String.append(t, SCon{' ', rest})),
        rr_and_l(rr_rc(B.char_class(c)), rr_all_rc(t), e)) : {_ == Some{SR.Split{SCon{c, t}, rest}} : rr_MS()}
      %rr_split_sp(t, rest, rr_and_r(rr_rc(B.char_class(c)), rr_all_rc(t), e)) : {SR.split.con(c, SR.split_sp(String.append(t, SCon{' ', rest}))) == SR.split.con(c, _) : rr_MS()}
      {==}

def rr_split_colon(+a: String, +rest: String, +e: {rr_all_nc(a) == True{} : Bool})
  -> {SR.split_colon(String.append(a, SCon{':', rest})) == Some{SR.Split{a, rest}} : rr_MS()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %rr_pick_colon(B.char_class(c), c, String.append(t, SCon{':', rest}), SR.split_colon(String.append(t, SCon{':', rest})),
        rr_and_l(rr_nc(B.char_class(c)), rr_all_nc(t), e)) : {_ == Some{SR.Split{SCon{c, t}, rest}} : rr_MS()}
      %rr_split_colon(t, rest, rr_and_r(rr_nc(B.char_class(c)), rr_all_nc(t), e)) : {SR.split.con(c, SR.split_colon(String.append(t, SCon{':', rest}))) == SR.split.con(c, _) : rr_MS()}
      {==}

def rr_fields(+hs: List<&2, M.Header>, +e: {rr_hdrs_good(hs) == True{} : Bool})
  -> {SR.fields(rr_texts(hs)) == Some{hs} : rr_MH()}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match h:
        case M.Header{+n, +v}:
          +eg = rr_and_l(rr_hdr_good(M.Header{n, v}), rr_hdrs_good(t), e)
          +et = rr_and_r(rr_hdr_good(M.Header{n, v}), rr_hdrs_good(t), e)
          +en = rr_and_l(rr_all_nc(n), rr_all_lc(v), eg)
          %Equal.sym(rr_MS(), SR.split_colon(String.append(n, SCon{':', SCon{' ', v}})), Some{SR.Split{n, SCon{' ', v}}},
            rr_split_colon(n, SCon{' ', v}, en)) : {SR.fields.con(SR.field.name(_), SR.fields(rr_texts(t))) == Some{Con{M.Header{n, v}, t}} : rr_MH()}
          %rr_fields(t, et) : {SR.fields.con(Some{M.Header{n, v}}, SR.fields(rr_texts(t))) == SR.fields.con(Some{M.Header{n, v}}, _) : rr_MH()}
          {==}

def rr_request_line(+mn: String, +t: String, +em: {rr_all_rc(mn) == True{} : Bool}, +et: {rr_all_rc(t) == True{} : Bool})
  -> {SR.request_line(rr_line0(mn, t)) == Some{SR.Split{mn, t}} : rr_MS()}:
  %Equal.sym(rr_MS(), SR.split_sp(String.append(mn, SCon{' ', String.append(t, " HTTP/1.1")})),
    Some{SR.Split{mn, String.append(t, " HTTP/1.1")}},
    rr_split_sp(mn, String.append(t, " HTTP/1.1"), em)) : {SR.request_line.method(_) == Some{SR.Split{mn, t}} : rr_MS()}
  %Equal.sym(rr_MS(), SR.split_sp(String.append(t, SCon{' ', "HTTP/1.1"})), Some{SR.Split{t, "HTTP/1.1"}},
    rr_split_sp(t, "HTTP/1.1", et)) : {SR.request_line.target(mn, _) == Some{SR.Split{mn, t}} : rr_MS()}
  {==}

# The whole request
# -----------------

def rr_main(+mn: String, +t: String, +hl: List<&2, M.Header>, +body: List<&2, U32>,
  +em: {rr_all_rc(mn) == True{} : Bool}, +et: {rr_all_rc(t) == True{} : Bool}, +eh: {rr_hdrs_good(hl) == True{} : Bool})
  -> {SR.decode_request(List.append(&2, U32, B.from_ascii.spec(String.append(mn, String.append(" ", String.append(t,
        String.append(" HTTP/1.1\r\n", String.append(E.header_lines.spec(hl), "\r\n")))))), body))
      == Some{SR.ParsedRequest{mn, t, hl, body}} : rr_MR()}:
  %rr_head_reshape(mn, t, String.append(E.header_lines.spec(hl), "\r\n")) : {SR.decode_request(List.append(&2, U32, B.from_ascii.spec(_), body)) == Some{SR.ParsedRequest{mn, t, hl, body}} : rr_MR()}
  %Equal.sym(rr_ML(), SR.head_lines.go(rr_lb(rr_line0(mn, t), String.append(E.header_lines.spec(hl), "\r\n"), body), SR.Start{}),
    Some{SR.Lines{Con{rr_line0(mn, t), rr_texts(hl)}, body}},
    rr_start_line(rr_line0(mn, t), String.append(E.header_lines.spec(hl), "\r\n"), body, rr_texts(hl), body,
      rr_all_lc_app(mn, String.append(" ", String.append(t, " HTTP/1.1")), rr_rc_lc_s(mn, em),
        rr_all_lc_app(t, " HTTP/1.1", rr_rc_lc_s(t, et), {==})),
      rr_nonnil_app(mn, String.append(" ", String.append(t, " HTTP/1.1")), {==}),
      rr_hdr_lines(hl, body, eh))) : {SR.decode.lines(_) == Some{SR.ParsedRequest{mn, t, hl, body}} : rr_MR()}
  %Equal.sym(rr_MS(), SR.request_line(rr_line0(mn, t)), Some{SR.Split{mn, t}}, rr_request_line(mn, t, em, et)) : {SR.decode.build(_, SR.fields(rr_texts(hl)), body) == Some{SR.ParsedRequest{mn, t, hl, body}} : rr_MR()}
  %Equal.sym(rr_MH(), SR.fields(rr_texts(hl)), Some{hl}, rr_fields(hl, eh)) : {SR.decode.build(Some{SR.Split{mn, t}}, _, body) == Some{SR.ParsedRequest{mn, t, hl, body}} : rr_MR()}
  {==}

def rr_law(+m: M.Method, +s: M.Scheme, +h: String, +p: Nat, +t: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  +e: {E.request_ok(M.Request{m, M.Url{s, h, p, t}, hs, body}) == True{} : Bool})
  -> {SR.decode_request(E.request_bytes(M.Request{m, M.Url{s, h, p, t}, hs, body}))
      == Some{SR.ParsedRequest{E.method_name(m), t, E.request_headers(M.Request{m, M.Url{s, h, p, t}, hs, body}), body}} : rr_MR()}:
  +ef = rr_and_l(E.fields_ok(m, M.Url{s, h, p, t}, hs, body), B.is_ascii(E.head_of(m, M.Url{s, h, p, t}, hs, body)), e)
  +ehk = rr_and_l(H.headers_ok(hs), Bool.and(E.none_reserved(hs), Bool.and(E.method_ok(m), Bool.and(U.ok(M.Url{s, h, p, t}), B.all_bytes(body)))), ef)
  +e1 = rr_and_r(H.headers_ok(hs), Bool.and(E.none_reserved(hs), Bool.and(E.method_ok(m), Bool.and(U.ok(M.Url{s, h, p, t}), B.all_bytes(body)))), ef)
  +e2 = rr_and_r(E.none_reserved(hs), Bool.and(E.method_ok(m), Bool.and(U.ok(M.Url{s, h, p, t}), B.all_bytes(body))), e1)
  +em = rr_and_l(E.method_ok(m), Bool.and(U.ok(M.Url{s, h, p, t}), B.all_bytes(body)), e2)
  +e3 = rr_and_r(E.method_ok(m), Bool.and(U.ok(M.Url{s, h, p, t}), B.all_bytes(body)), e2)
  +eu = rr_and_l(U.ok(M.Url{s, h, p, t}), B.all_bytes(body), e3)
  +eth = rr_and_r(Bool.and(U.host_ok(h), U.port_ok(p)), U.target_ok(t), eu)
  +ehp = rr_and_l(Bool.and(U.host_ok(h), U.port_ok(p)), U.target_ok(t), eu)
  +eho = rr_and_l(U.host_ok(h), U.port_ok(p), ehp)
  +ehc = rr_and_l(U.host_chars(h), U.numeric_ok(h), eho)
  +ehs = Equal.trans(Bool, H.headers_ok.spec(hs), H.headers_ok(hs), True{},
    Equal.sym(Bool, H.headers_ok.go(hs, True{}), Bool.and(True{}, H.headers_ok.spec(hs)), rr_hok_go(hs, True{})),
    ehk)
  %rr_onto(E.head_of(m, M.Url{s, h, p, t}, hs, body), body) : {SR.decode_request(_) == Some{SR.ParsedRequest{E.method_name(m), t, E.request_headers(M.Request{m, M.Url{s, h, p, t}, hs, body}), body}} : rr_MR()}
  %rr_hl_spec(E.headers_of(m, M.Url{s, h, p, t}, hs, body)) : {SR.decode_request(List.append(&2, U32, B.from_ascii.spec(String.append(E.method_name(m), String.append(" ", String.append(t, String.append(" HTTP/1.1\r\n", String.append(_, "\r\n")))))), body)) == Some{SR.ParsedRequest{E.method_name(m), t, E.request_headers(M.Request{m, M.Url{s, h, p, t}, hs, body}), body}} : rr_MR()}
  rr_main(E.method_name(m), t, E.headers_of(m, M.Url{s, h, p, t}, hs, body), body,
    rr_method_rc(m, em), rr_target_ok_rc(t, eth),
    rr_hl_good(m, s, h, p, t, hs, body, ehs, rr_host_chars_lc(h, ehc)))

def Laws.request_roundtrip(m, s, h, p, t, hs, body, e):
  rr_law(m, s, h, p, t, hs, body, e)
