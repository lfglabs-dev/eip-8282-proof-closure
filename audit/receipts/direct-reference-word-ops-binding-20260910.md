# Reference word operations

ReferenceWordOps is a local, audited transcription of immutable execution-specs Amsterdam instructions at 0cc100eb190b64b23baba72dac0165652eaec252. Source-to-transcription remains a trust boundary. The theorem checks pinned EVMYul Lean word functions and actual raw successful stack effects against the transcription; it does not execute Python or establish full interpreter refinement.

ADD/MUL use remainder modulo2^256; SUB uses (2^256-y+x) modulo2^256 for typed words. DIV explicitly returns0 on divisor0. LT/GT/EQ/ISZERO return0 or1. AND uses natural bitwise AND with bounded inputs. SHL pops shift then value and uses the source's mask by2^256−1 under shift<256; otherwise0. SHR similarly returns0 when shift≥256.

Python stacks pop the last list element and append results. fromPython reverses the list. Thus prefix++[y,x] maps to x::y::reverse(prefix), and the result is appended in Python/head-consed in Lean. No operand order is inferred from commutativity.

Remaining boundaries: actual Python numeric library implementation, stack and gas error control flow, gas-cost parity, memory and environment effects, and Python Uint versus Lean word PC representation. Successful raw-stack effect does not assert Z/transaction admission or gas adequacy. Each Lean reference operation is independent natural arithmetic; the pinned evaluator itself is unchanged.

Fullsource paths/hashes are in sources.json. Arithmetic, comparison and stack were fetched only from immutable0cc URLs. Existing archived bitwise source reused.
