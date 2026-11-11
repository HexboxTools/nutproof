/-!
# nutproof part 2: NUT-11 P2PK Schnorr signatures and the mint's value-conservation invariant

Same model as NutProof.lean: points are represented by their discrete log in a field `F`
(instantiate F := ZMod n for secp256k1), so `sG` is `s` and `e·P` is `e * P`.
Amounts are natural numbers (sats), fees follow NUT-02 (`input_fee_ppk`, rounded up).
-/

namespace NutProof.P2PK
variable {F : Type} [Lean.Grind.Field F]

/-! ## NUT-11: BIP340 Schnorr over the P2PK lock key -/

/-- Signer with secret x (public P = xG), nonce r (R = rG), challenge e = H(R ‖ P ‖ m):
response s = r + e x. -/
def schnorrS (r e x : F) : F := r + e * x
/-- Verifier (the mint) accepts (R, s) for P iff sG = R + eP. -/
def schnorrVerify (P R s e : F) : Prop := s = R + e * P

/-- Completeness: an honestly produced witness signature always passes the mint's check. -/
theorem schnorr_complete (x r e : F) : schnorrVerify x r (schnorrS r e x) e := by
  unfold schnorrVerify schnorrS; grind

/-- Special soundness: two accepting signatures with the same nonce R and different challenges
reveal the lock key's secret. So only the holder of x can keep producing valid witnesses, and
reusing a nonce across two proofs leaks the key (why NUT-11 wallets must use fresh nonces). -/
theorem schnorr_special_soundness (P R s s' e e' : F) (hne : e ≠ e')
    (h : schnorrVerify P R s e) (h' : schnorrVerify P R s' e') :
    P = (s - s') / (e - e') := by
  unfold schnorrVerify at *
  have hd : e - e' ≠ 0 := by grind
  have : s - s' = (e - e') * P := by grind
  grind

/-- Nonce reuse attack, concretely: from two honest signatures with the same nonce on
different challenges, anyone recovers x. -/
theorem nonce_reuse_leaks_key (x r e e' : F) (hne : e ≠ e') :
    x = (schnorrS r e x - schnorrS r e' x) / (e - e') := by
  unfold schnorrS
  have hd : e - e' ≠ 0 := by grind
  grind

/-- A signature made with a different key does not verify for P (unless e = 0). -/
theorem wrong_key_rejected (x P r e : F) (hP : P ≠ x) (he : e ≠ 0) :
    ¬ schnorrVerify P r (schnorrS r e x) e := by
  unfold schnorrVerify schnorrS; intro h
  have : e * (x - P) = 0 := by grind
  grind

/-! ## NUT-11 multisig: `n_sigs` of the listed pubkeys (count distinct valid signers) -/

/-- Number of listed pubkeys that produced a valid signature. -/
def validCount (ok : List Bool) : Nat := (ok.filter id).length

theorem validCount_le (ok : List Bool) : validCount ok ≤ ok.length := by
  unfold validCount; exact List.length_filter_le _ _

/-- A threshold above the number of listed keys can never be met: such a proof is unspendable
(a wallet-side sanity check NUT-11 implementations should enforce). -/
theorem threshold_unreachable (ok : List Bool) (n : Nat) (h : ok.length < n) :
    ¬ n ≤ validCount ok := by
  have := validCount_le ok; omega

end NutProof.P2PK

namespace NutProof.Ledger

/-! ## Mint ledger: value conservation for swap (NUT-03) and melt (NUT-05) with NUT-02 fees -/

/-- NUT-02 fee: sum of per-input `input_fee_ppk`, divided by 1000, rounded up. -/
def fee (ppks : List Nat) : Nat := (ppks.sum + 999) / 1000

/-- Fee is zero iff every keyset charges 0 ppk. -/
theorem fee_zero_iff (ppks : List Nat) : fee ppks = 0 ↔ ppks.sum = 0 := by
  unfold fee; omega

/-- Fees never exceed one sat per input when each keyset charges at most 1000 ppk. -/
theorem fee_le_inputs (ppks : List Nat) (h : ∀ p ∈ ppks, p ≤ 1000) : fee ppks ≤ ppks.length := by
  unfold fee
  have : ppks.sum ≤ 1000 * ppks.length := by
    induction ppks with
    | nil => simp
    | cons a t ih =>
      simp only [List.sum_cons, List.length_cons]
      have ha := h a (by simp)
      have := ih (fun p hp => h p (by simp [hp]))
      omega
  omega

/-- Mint state: total value of unspent ecash outstanding, and fees the mint has kept. -/
structure State where
  outstanding : Nat
  feesKept : Nat
  backing : Nat   -- sats the mint holds (Lightning/on-chain reserve)

/-- Solvency invariant: reserves cover all outstanding ecash plus kept fees. -/
def Solvent (s : State) : Prop := s.outstanding + s.feesKept ≤ s.backing

/-- A swap is accepted only when Σinputs = Σoutputs + fee(inputs). -/
def swapOk (ins outs : List Nat) (ppks : List Nat) : Prop := ins.sum = outs.sum + fee ppks

def swap (s : State) (ins outs : List Nat) (ppks : List Nat) : State :=
  { s with outstanding := s.outstanding - ins.sum + outs.sum, feesKept := s.feesKept + fee ppks }

/-- No inflation: an accepted swap never creates value. -/
theorem swap_no_inflation (ins outs ppks : List Nat) (h : swapOk ins outs ppks) :
    outs.sum ≤ ins.sum := by unfold swapOk at h; omega

/-- Swaps preserve outstanding + feesKept exactly (value only changes hands), hence solvency. -/
theorem swap_conserves (s : State) (ins outs ppks : List Nat) (hin : ins.sum ≤ s.outstanding)
    (h : swapOk ins outs ppks) :
    (swap s ins outs ppks).outstanding + (swap s ins outs ppks).feesKept
      = s.outstanding + s.feesKept := by
  unfold swap swapOk at *; simp only; omega

theorem swap_solvent (s : State) (ins outs ppks : List Nat) (hin : ins.sum ≤ s.outstanding)
    (h : swapOk ins outs ppks) (hs : Solvent s) : Solvent (swap s ins outs ppks) := by
  have := swap_conserves s ins outs ppks hin h
  unfold Solvent at *; unfold swap at *; simp only at *; omega

/-- Melt (NUT-05): burn inputs, pay `amount` + actual Lightning fee `lnFee` out of reserves,
return change ecash; accepted when Σinputs = amount + feeReserve + fee(inputs) and
lnFee ≤ feeReserve, change = feeReserve - lnFee (NUT-08). -/
def meltOk (ins : List Nat) (amount feeReserve lnFee : Nat) (ppks : List Nat) : Prop :=
  ins.sum = amount + feeReserve + fee ppks ∧ lnFee ≤ feeReserve

def melt (s : State) (ins : List Nat) (amount feeReserve lnFee : Nat) (ppks : List Nat) : State :=
  { outstanding := s.outstanding - ins.sum + (feeReserve - lnFee)
    feesKept := s.feesKept + fee ppks
    backing := s.backing - (amount + lnFee) }

/-- Melting with NUT-08 change returned keeps the mint solvent. -/
theorem melt_solvent (s : State) (ins : List Nat) (amount feeReserve lnFee : Nat) (ppks : List Nat)
    (hin : ins.sum ≤ s.outstanding) (h : meltOk ins amount feeReserve lnFee ppks)
    (hs : Solvent s) : Solvent (melt s ins amount feeReserve lnFee ppks) := by
  unfold Solvent melt meltOk at *; simp only at *; omega

/-- Mint (NUT-04): after a paid invoice of `amount`, issue outputs summing to `amount`. -/
def mintOk (amount : Nat) (outs : List Nat) : Prop := outs.sum = amount
def mint (s : State) (amount : Nat) (outs : List Nat) : State :=
  { s with outstanding := s.outstanding + outs.sum, backing := s.backing + amount }

theorem mint_solvent (s : State) (amount : Nat) (outs : List Nat) (h : mintOk amount outs)
    (hs : Solvent s) : Solvent (mint s amount outs) := by
  unfold Solvent mint mintOk at *; simp only at *; omega

end NutProof.Ledger

#print axioms NutProof.P2PK.schnorr_special_soundness
#print axioms NutProof.Ledger.melt_solvent
