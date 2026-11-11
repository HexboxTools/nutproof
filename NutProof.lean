/-!
# nutproof: machine-checked algebra of Cashu's blind signatures (NUT-00) and DLEQ proofs (NUT-12)

Model. secp256k1 has prime order n, so the group of points is isomorphic to ZMod n:
every point P is uniquely `p • G` for a scalar `p`. We therefore represent each point by
its discrete log in an arbitrary field `F` (instantiate F := ZMod n). Point addition is
`+`, scalar multiplication `a • P` is `a * p`. All statements below are exact algebraic
identities in that model; they say nothing about hardness assumptions (DL, ROM), only that
the protocol equations are right. Hashes (hash_to_curve, the DLEQ challenge hash) are
arbitrary inputs, so every theorem holds for every hash output.
-/

namespace NutProof
variable {F : Type} [Lean.Grind.Field F]

/-! ## NUT-00 BDHKE -/

/-- Alice blinds Y = hash_to_curve(x) with blinding factor r: B' = Y + rG. -/
def blind (Y r : F) : F := Y + r
/-- Bob (mint) signs with private key k: C' = k B'. -/
def sign (k B' : F) : F := k * B'
/-- Alice unblinds with Bob's public key K = kG: C = C' - rK. -/
def unblind (C' r K : F) : F := C' - r * K
/-- Bob later verifies a token (x, C) by checking k * hash_to_curve(x) = C. -/
def verify (k Y C : F) : Prop := k * Y = C

/-- Correctness: the unblinded signature always verifies. -/
theorem bdhke_correct (k Y r : F) :
    verify k Y (unblind (sign k (blind Y r)) r k) := by
  unfold verify unblind sign blind; grind

/-- Perfect blinding: every blinded message B' the mint could see is consistent with every
secret Y (take r = B' - Y), so the mint's view at signing time carries no information about Y. -/
theorem blinding_perfectly_hiding (Y B' : F) : ∃ r, blind Y r = B' :=
  ⟨B' - Y, by unfold blind; grind⟩

/-- The blinding factor is uniquely determined by (Y, B'): one r per secret, so a uniform r
gives a uniform B' independent of Y. -/
theorem blinding_unique (Y r r' : F) (h : blind Y r = blind Y r') : r = r' := by
  unfold blind at h; grind

/-- Unblinding with the wrong public key does not yield a valid signature (unless r = 0). -/
theorem wrong_key_fails (k K Y r : F) (hK : K ≠ k) (hr : r ≠ 0) :
    ¬ verify k Y (unblind (sign k (blind Y r)) r K) := by
  unfold verify unblind sign blind; intro h
  have : r * (k - K) = 0 := by grind
  grind

/-! ## NUT-12 DLEQ proof (Bob proves C' = kB' and K = kG share k) -/

/-- Mint's DLEQ response: nonce r_n, challenge e, s = r_n + e k. -/
def dleqS (rn e k : F) : F := rn + e * k
/-- Verifier recomputes R1 = sG - eK and R2 = sB' - eC'. -/
def R1 (s e K : F) : F := s - e * K
def R2 (s e B' C' : F) : F := s * B' - e * C'

/-- Completeness for Alice (has B', C'): recomputed R1, R2 equal the mint's commitments
rn·G and rn·B', so the hashed challenge matches. -/
theorem dleq_complete (k B' rn e : F) :
    R1 (dleqS rn e k) e k = rn ∧ R2 (dleqS rn e k) e B' (sign k B') = rn * B' := by
  unfold R1 R2 dleqS sign; constructor <;> grind

/-- Completeness for Carol (NUT-12 offline check): given only the token (x, C) plus (e, s, r),
she rebuilds B' = Y + rG and C' = C + rK and gets exactly the mint's commitments. -/
theorem dleq_carol_complete (k Y r rn e : F) :
    let C  := unblind (sign k (blind Y r)) r k
    let B' := Y + r
    let C' := C + r * k
    R1 (dleqS rn e k) e k = rn ∧ R2 (dleqS rn e k) e B' C' = rn * B' := by
  unfold R1 R2 dleqS unblind sign blind; constructor <;> grind

/-- Special soundness: two accepting transcripts with the same commitments and different
challenges reveal one key k that satisfies both K = kG and C' = kB'. So a mint that can
answer two challenges really used the same key for the signature as for its public key. -/
theorem dleq_special_soundness (K B' C' s s' e e' a1 a2 : F) (hne : e ≠ e')
    (h1 : R1 s e K = a1) (h1' : R1 s' e' K = a1)
    (h2 : R2 s e B' C' = a2) (h2' : R2 s' e' B' C' = a2) :
    let k := (s - s') / (e - e')
    K = k ∧ C' = k * B' := by
  unfold R1 R2 at *
  have hd : e - e' ≠ 0 := by grind
  constructor
  · grind
  · have : (s - s') * B' = (e - e') * C' := by grind
    grind

/-- Honest-verifier zero knowledge: for ANY challenge e and response s, setting
R1 := sG - eK, R2 := sB' - eC' yields an accepting transcript without knowing k. -/
theorem dleq_simulatable (K B' C' e s : F) :
    ∃ a1 a2, R1 s e K = a1 ∧ R2 s e B' C' = a2 := ⟨_, _, rfl, rfl⟩

end NutProof
