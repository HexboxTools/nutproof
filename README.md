# nutproof — machine-checked algebra of Cashu ecash (Lean 4, no Mathlib, no sorry)

Built Nov 10 2026 for [Nut November](https://nutnovember.org/). https://github.com/HexboxTools/nutproof

`lake build` (Lean 4.34, no Mathlib, `grind` field solver) checks:
- NUT-00 BDHKE: unblinded signature always verifies; blinding is perfectly hiding and the
  blinding factor is unique; unblinding with a wrong mint key fails.
- NUT-12 DLEQ: completeness for Alice and for Carol's offline re-blinded check; special
  soundness (two challenges extract one k with K=kG and C'=kB'); HVZK simulatability.
Model: prime-order group ≅ ZMod n, points as discrete logs over any field F. Algebra only —
no hardness/ROM claims. `#print axioms` = propext, Classical.choice, Quot.sound only.

`lean P2PKLedger.lean` adds:
- NUT-11 P2PK (BIP340 Schnorr): completeness, special soundness, nonce reuse leaks the key,
  wrong key rejected; multisig: a threshold above the key count is unspendable.
- Mint ledger with NUT-02 fees: fee = ceil(sum ppk / 1000), fee <= #inputs when ppk <= 1000;
  swap never inflates and conserves outstanding+fees; swap, melt (NUT-05 with NUT-08 change)
  and mint (NUT-04) all preserve solvency (reserves >= outstanding ecash + kept fees).

Standalone `lean NutProof.lean` / `lean P2PKLedger.lean` / `lean DoubleSpend.lean` also check.

`cd harness && npm i && npm test` ties the model to real secp256k1 bytes: NUT-00 spec
hash_to_curve vectors, plus 104 checks of the exact proved equations (BDHKE, DLEQ incl.
Carol's offline check and key extraction, BIP340 P2PK) on the real curve.

`lean DoubleSpend.lean` adds the mint's spent-set model (NUT-00 Y values, NUT-07 checkstate):
atomic accept/reject, rejected requests are no-ops, the spent set is monotone, every accepted Y
is recorded, replays are rejected, and over ANY request sequence a Y is accepted at most once
(no hash_to_curve injectivity assumed). Axioms: propext, Quot.sound only.

Roadmap: NUT-13 deterministic secrets, NUT-10 secret well-formedness.
