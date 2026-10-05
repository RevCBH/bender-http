# The proofs of LAWS.bend. Each file under proofs/ proves a group of laws
# (`def Laws.<name>`) with its own lemmas. The gate:
#   bend PROOF.bend             ALL PROOFS CHECK once every law is proven
#   bend PROOF.bend --verdict   the same, rechecked by the BendTT kernel (Lean)
import Base
import ./LAWS.bend as Laws
import ./proofs/url_concrete.bend as P_url_concrete
import ./proofs/num.bend as P_num
import ./proofs/decode_lemmas.bend as P_decode_lemmas
import ./proofs/headers.bend as P_headers
import ./proofs/url.bend as P_url
import ./proofs/encode_basic.bend as P_encode_basic
import ./proofs/request_roundtrip.bend as P_request_roundtrip
import ./proofs/decode_basic.bend as P_decode_basic
import ./proofs/decode_head.bend as P_decode_head
import ./proofs/response_length.bend as P_response_length
import ./proofs/response_close.bend as P_response_close
import ./proofs/response_chunked.bend as P_response_chunked
