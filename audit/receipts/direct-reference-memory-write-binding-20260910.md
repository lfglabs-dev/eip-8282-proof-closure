# Actual sparse memory write interface

Frozen source SHA256 c28fdb1241db9b1b640e96d143b465104284a1187ea5eb2f5e689121bac2f053, final targeted34369 exit0, olean emitted. Two exports standard axioms only; no warnings. Log /tmp/eip-reference-memory-write-compile.log SHA256 afba879e2ff41695e349b8632bcf7bbad003010bc69cc76bd5896a6bff105759.

`ReferenceMemoryWrite.write_byte src dst so dest len i bounds` gives the exact byte of actual ByteArray.write: inside [dest,dest+len), zero-extended source byte at so+(i-dest); elsewhere old destination byte. Proof unfolds the actual ByteArray.write/copySlice branches and normalizes all array reads; no predicted post-memory relation is supplied.

Bounds is len=0 OR (len<2^hostBits AND (so<src.size -> dest-dst.size<2^hostBits)). Thus zero-length writes impose no bounds, and arbitrarily large out-of-range source offsets impose no destination-gap premise. In-range source writes use exact host padding bounds; allocated source padding is <=len. Physical destination need not extend through an all-zero written suffix.

`congr` consumes Same sources and Same destinations plus each concrete write's own Bounds. It yields Same resulting actual writes, despite different physical zero suffixes. It does not assert equal ByteArray lengths or equal arrays. It is suitable for composing sparse pinned memory with rounded reference memory once the reference write observation and capacity/resource producers are proved.

The theorem concerns Lean's actual byte-array functions, not Python runtime/host allocation refinement. No gas sufficiency, source buffer implementation, access-bound producer or protocol adoption is claimed. Early checks exposed proof-normalization issues; the final exact source has no sorry/native_decide/custom axioms.
