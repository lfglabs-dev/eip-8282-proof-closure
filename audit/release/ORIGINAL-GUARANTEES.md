# Original requested guarantees (preserved)

These are the guarantees supplied by Thomas, before the authorized audit-domain
revision of 10 September 2026. They are not replaced in the pinned EIP.

## P-SUBMIT-1

This would protect admission. Only a well-formed, paid, non-inhibited user call
could append exactly one authentic record and emit one LOG0 of that record.

- Paid means msg.value is at least the quoted fee, and for a deposit also amount * 1 gwei.
- A deposit record is exactly the 184-byte calldata (the contract does not check the signature).
- An exit record is msg.sender || pubkey: the caller supplies only the 48-byte pubkey.
- For exit again, source_address is copied from msg.sender, not from calldata.
- Non-inhibited means slot 0 is not INHIBITOR (2^256−1) and when inhibited, every non-SYSTEM call reverts.

## P-DRAIN-1

This would protect consumption. Only a SYSTEM call could pop records from the
queue while a user call, including the fee getter, could not.

- Pop means return the oldest n = min(length, cap) records as one contiguous buffer, then move the pointers: full drain (n = length) sets HEAD and TAIL to 0. Partial drain sets HEAD += n and leaves TAIL.
- Cap is 64 deposits, 16 exits.
- A deposit's amount is recoded big-endian in storage to little-endian in that return.
- An exit record is returned as stored (source_address || pubkey).
- Drain does not zero the old record slots (words from slot 4 up stay).
- Length is TAIL - HEAD on the packed queue (slots 2 and 3).

## P-CONTROL-1

This would protect how excess, count, and INHIBITOR are updated.

- msg.sender alone chooses the user path vs the system path.
- INHIBITOR blocks users but never SYSTEM.
- User path: empty calldata and value = 0 is a quote (32-byte fee, no write, HEAD/TAIL unchanged). A successful paid append increments count by 1 and leaves excess unchanged.
- System path: count is set to 0. If calldata is nonempty, slot 0 becomes INHIBITOR. If already inhibited and calldata is empty, slot 0 becomes 0 (unlock). Otherwise slot 0 becomes max(0, excess + count − TARGET) with TARGET 8 (deposit) / 2 (exit).
- INHIBITOR is 2^256−1 in slot 0. Exit's constructor writes it (users off until the first empty SYSTEM call). Deposit's constructor does not (starts enabled).
- The quoted fee uses fake_exponential(1, excess + max(0, count − TARGET), 17). That numerator is not the same as the value empty SYSTEM later stores.
