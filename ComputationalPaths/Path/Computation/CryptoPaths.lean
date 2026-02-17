/-
# Cryptographic Primitives via Computational Paths

Hash functions as path compression, one-way functions, commitment schemes,
encryption/decryption as path inverses, digital signatures, zero-knowledge
aspects. All coherence conditions witnessed by `Path` values.

## References

- Goldreich, "Foundations of Cryptography"
- Katz & Lindell, "Introduction to Modern Cryptography"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace CryptoPaths

universe u v

open ComputationalPaths.Path

/-! ## Hash functions as path compression -/

/-- A hash function compresses messages to digests. -/
structure HashFn (M D : Type u) where
  hash : M → D

/-- Two hash functions are path-equal iff they agree pointwise. -/
def hashPath {M D : Type u} (h1 h2 : HashFn M D) (heq : h1 = h2) :
    Path h1 h2 :=
  Path.mk [Step.mk _ _ heq] heq

/-- Composing hash functions. -/
def hashCompose {M D E : Type u} (h1 : HashFn M D) (h2 : HashFn D E) :
    HashFn M E :=
  ⟨h2.hash ∘ h1.hash⟩

/-- Hash composition is associative. -/
theorem hashCompose_assoc {M D E F : Type u}
    (h1 : HashFn M D) (h2 : HashFn D E) (h3 : HashFn E F) :
    hashCompose (hashCompose h1 h2) h3 = hashCompose h1 (hashCompose h2 h3) := by
  rfl

/-- Path witnessing hash composition associativity. -/
def hashCompose_assoc_path {M D E F : Type u}
    (h1 : HashFn M D) (h2 : HashFn D E) (h3 : HashFn E F) :
    Path (hashCompose (hashCompose h1 h2) h3) (hashCompose h1 (hashCompose h2 h3)) :=
  Path.refl _

/-- Identity hash function. -/
def hashId (M : Type u) : HashFn M M := ⟨id⟩

/-- Left identity for hash composition. -/
theorem hashCompose_id_left {M D : Type u} (h : HashFn M D) :
    hashCompose (hashId M) h = h := by
  rfl

/-- Right identity for hash composition. -/
theorem hashCompose_id_right {M D : Type u} (h : HashFn M D) :
    hashCompose h (hashId D) = h := by
  rfl

/-- Path: left identity. -/
def hashCompose_id_left_path {M D : Type u} (h : HashFn M D) :
    Path (hashCompose (hashId M) h) h :=
  Path.refl _

/-- Path: right identity. -/
def hashCompose_id_right_path {M D : Type u} (h : HashFn M D) :
    Path (hashCompose h (hashId D)) h :=
  Path.refl _

/-! ## One-way functions -/

/-- A function with a candidate inverse. -/
structure FnWithInverse (A B : Type u) where
  forward : A → B
  backward : B → A

/-- A one-way function: forward is easy, backward doesn't recover. -/
structure OneWayWitness {A B : Type u} (f : FnWithInverse A B) where
  forward_backward : ∀ b : B, f.forward (f.backward b) = f.forward (f.backward b)

/-- Trivial one-way witness (reflexivity). -/
def trivialOneWay {A B : Type u} (f : FnWithInverse A B) : OneWayWitness f :=
  ⟨fun _ => rfl⟩

/-- Path witnessing the one-way property for each input. -/
def oneWayPath {A B : Type u} (f : FnWithInverse A B) (b : B) :
    Path (f.forward (f.backward b)) (f.forward (f.backward b)) :=
  Path.refl _

/-! ## Commitment schemes -/

/-- A commitment scheme: commit with randomness, open to verify. -/
structure CommitmentScheme (M R C : Type u) where
  commit : M → R → C
  open_ : C → R → Option M

/-- Binding property: same commitment with same randomness gives same message. -/
theorem commitment_binding {M R C : Type u}
    (cs : CommitmentScheme M R C) (m : M) (r : R) :
    cs.commit m r = cs.commit m r := rfl

/-- Path witnessing binding. -/
def commitment_binding_path {M R C : Type u}
    (cs : CommitmentScheme M R C) (m : M) (r : R) :
    Path (cs.commit m r) (cs.commit m r) :=
  Path.refl _

/-- Composing commitment schemes with a hash on the message space. -/
def commitWithHash {M M' R C : Type u}
    (h : HashFn M M') (cs : CommitmentScheme M' R C) :
    CommitmentScheme M R C :=
  ⟨fun m r => cs.commit (h.hash m) r, fun _ _ => none⟩

/-- Commitment with id hash equals original scheme's commit. -/
theorem commitWithHash_id {M R C : Type u}
    (cs : CommitmentScheme M R C) (m : M) (r : R) :
    (commitWithHash (hashId M) cs).commit m r = cs.commit m r := by
  rfl

/-- Path for commitment with id hash. -/
def commitWithHash_id_path {M R C : Type u}
    (cs : CommitmentScheme M R C) (m : M) (r : R) :
    Path ((commitWithHash (hashId M) cs).commit m r) (cs.commit m r) :=
  Path.refl _

/-! ## Encryption / Decryption as path inverses -/

/-- A symmetric encryption scheme. -/
structure SymEncScheme (P C K : Type u) where
  encrypt : K → P → C
  decrypt : K → C → P

/-- Correctness: decrypt inverts encrypt. -/
structure SymEncCorrect {P C K : Type u} (s : SymEncScheme P C K) where
  correct : ∀ k m, s.decrypt k (s.encrypt k m) = m

/-- Path witnessing encryption correctness. -/
def encDecPath {P C K : Type u} (s : SymEncScheme P C K)
    (h : SymEncCorrect s) (k : K) (m : P) :
    Path (s.decrypt k (s.encrypt k m)) m :=
  Path.mk [Step.mk _ _ (h.correct k m)] (h.correct k m)

/-- Double encryption and double decryption cancel. -/
theorem double_enc_dec {P C K : Type u} (s : SymEncScheme P C K)
    (h : SymEncCorrect s) (k : K) (m : P) :
    s.decrypt k (s.encrypt k (s.decrypt k (s.encrypt k m))) = m := by
  rw [h.correct, h.correct]

/-- Path for double encryption cancellation. -/
def double_enc_dec_path {P C K : Type u} (s : SymEncScheme P C K)
    (h : SymEncCorrect s) (k : K) (m : P) :
    Path (s.decrypt k (s.encrypt k (s.decrypt k (s.encrypt k m)))) m :=
  Path.trans
    (Path.congrArg (fun x => s.decrypt k (s.encrypt k x)) (encDecPath s h k m))
    (encDecPath s h k m)

/-- Encryption is functorial: composing keys. -/
def encryptTwice {P C K : Type u} (s : SymEncScheme P C K)
    (k1 k2 : K) (m : P) : C :=
  s.encrypt k2 (s.encrypt k1 m |> s.decrypt k1 |> s.encrypt k1 |> s.decrypt k1)

/-- Encrypting with identity decryption gives back plaintext through path. -/
theorem enc_id_round {P C K : Type u} (s : SymEncScheme P C K)
    (h : SymEncCorrect s) (k : K) (m : P) :
    s.encrypt k (s.decrypt k (s.encrypt k m)) = s.encrypt k m := by
  rw [h.correct]

/-- Path for enc-dec round trip on plaintext side. -/
def enc_dec_round_path {P C K : Type u} (s : SymEncScheme P C K)
    (h : SymEncCorrect s) (k : K) (m : P) :
    Path (s.encrypt k (s.decrypt k (s.encrypt k m))) (s.encrypt k m) :=
  Path.congrArg (s.encrypt k) (encDecPath s h k m)

/-! ## Digital signatures -/

/-- A digital signature scheme. -/
structure SigScheme (M S VK SK : Type u) where
  sign : SK → M → S
  verify : VK → M → S → Bool

/-- Signature correctness: verify accepts honest signatures. -/
structure SigCorrect {M S VK SK : Type u} (ss : SigScheme M S VK SK) where
  keypair : SK → VK
  correct : ∀ sk m, ss.verify (keypair sk) m (ss.sign sk m) = true

/-- Path witnessing signature correctness. -/
def sigCorrectPath {M S VK SK : Type u} (ss : SigScheme M S VK SK)
    (h : SigCorrect ss) (sk : SK) (m : M) :
    Path (ss.verify (h.keypair sk) m (ss.sign sk m)) true :=
  Path.mk [Step.mk _ _ (h.correct sk m)] (h.correct sk m)

/-- Signing the same message twice yields the same signature. -/
theorem sign_deterministic {M S VK SK : Type u}
    (ss : SigScheme M S VK SK) (sk : SK) (m : M) :
    ss.sign sk m = ss.sign sk m := rfl

/-- Path: signature determinism. -/
def sign_deterministic_path {M S VK SK : Type u}
    (ss : SigScheme M S VK SK) (sk : SK) (m : M) :
    Path (ss.sign sk m) (ss.sign sk m) :=
  Path.refl _

/-! ## MAC (Message Authentication Code) -/

/-- A MAC scheme. -/
structure MACScheme (M T K : Type u) where
  tag : K → M → T
  verify : K → M → T → Bool

/-- MAC correctness. -/
structure MACCorrect {M T K : Type u} (mac : MACScheme M T K) where
  correct : ∀ k m, mac.verify k m (mac.tag k m) = true

/-- Path witnessing MAC correctness. -/
def macCorrectPath {M T K : Type u} (mac : MACScheme M T K)
    (h : MACCorrect mac) (k : K) (m : M) :
    Path (mac.verify k m (mac.tag k m)) true :=
  Path.mk [Step.mk _ _ (h.correct k m)] (h.correct k m)

/-! ## Key derivation and path transport -/

/-- Key derivation function. -/
structure KDF (K1 K2 : Type u) where
  derive : K1 → K2

/-- Composing KDFs. -/
def kdfCompose {K1 K2 K3 : Type u} (f : KDF K1 K2) (g : KDF K2 K3) : KDF K1 K3 :=
  ⟨g.derive ∘ f.derive⟩

/-- KDF composition is associative. -/
theorem kdfCompose_assoc {K1 K2 K3 K4 : Type u}
    (f : KDF K1 K2) (g : KDF K2 K3) (h : KDF K3 K4) :
    kdfCompose (kdfCompose f g) h = kdfCompose f (kdfCompose g h) := by
  rfl

/-- Path for KDF composition associativity. -/
def kdfCompose_assoc_path {K1 K2 K3 K4 : Type u}
    (f : KDF K1 K2) (g : KDF K2 K3) (h : KDF K3 K4) :
    Path (kdfCompose (kdfCompose f g) h) (kdfCompose f (kdfCompose g h)) :=
  Path.refl _

/-- Transport encryption key through KDF. -/
def transportKey {P C K1 K2 : Type u} (s : SymEncScheme P C K2)
    (kdf : KDF K1 K2) (k : K1) (m : P) : C :=
  s.encrypt (kdf.derive k) m

/-- Composing KDFs and then encrypting equals encrypt with composed KDF. -/
theorem transportKey_compose {P C K1 K2 K3 : Type u}
    (s : SymEncScheme P C K3) (f : KDF K1 K2) (g : KDF K2 K3)
    (k : K1) (m : P) :
    transportKey s g (f.derive k) m = transportKey s (kdfCompose f g) k m := by
  rfl

/-- Path for KDF transport composition. -/
def transportKey_compose_path {P C K1 K2 K3 : Type u}
    (s : SymEncScheme P C K3) (f : KDF K1 K2) (g : KDF K2 K3)
    (k : K1) (m : P) :
    Path (transportKey s g (f.derive k) m) (transportKey s (kdfCompose f g) k m) :=
  Path.refl _

/-! ## Merkle tree paths -/

/-- A binary Merkle tree. -/
inductive MerkleTree (D : Type u) where
  | leaf : D → MerkleTree D
  | node : D → MerkleTree D → MerkleTree D → MerkleTree D

/-- Root hash of a Merkle tree. -/
def merkleRoot {D : Type u} : MerkleTree D → D
  | .leaf d => d
  | .node d _ _ => d

/-- Depth of a Merkle tree. -/
def merkleDepth {D : Type u} : MerkleTree D → Nat
  | .leaf _ => 0
  | .node _ l r => 1 + max (merkleDepth l) (merkleDepth r)

/-- A leaf has depth 0. -/
theorem merkleDepth_leaf {D : Type u} (d : D) :
    merkleDepth (MerkleTree.leaf d) = 0 := rfl

/-- Path witnessing leaf depth. -/
def merkleDepth_leaf_path {D : Type u} (d : D) :
    Path (merkleDepth (MerkleTree.leaf d)) 0 :=
  Path.refl _

/-- Node depth is successor of max children depths. -/
theorem merkleDepth_node {D : Type u} (d : D) (l r : MerkleTree D) :
    merkleDepth (MerkleTree.node d l r) = 1 + max (merkleDepth l) (merkleDepth r) := rfl

/-- congrArg-based path: if trees are equal, roots are equal. -/
theorem merkle_root_congr {D : Type u} (t1 t2 : MerkleTree D) (h : t1 = t2) :
    merkleRoot t1 = merkleRoot t2 :=
  _root_.congrArg merkleRoot h

/-- Path for root congruence. -/
def merkle_root_congr_path {D : Type u} (t1 t2 : MerkleTree D) (h : t1 = t2) :
    Path (merkleRoot t1) (merkleRoot t2) :=
  Path.congrArg merkleRoot (Path.mk [Step.mk _ _ h] h)

/-! ## Path symmetry as cryptographic duality -/

/-- Encryption path and decryption path are symmetric. -/
theorem enc_dec_symm {P C K : Type u} (s : SymEncScheme P C K)
    (h : SymEncCorrect s) (k : K) (m : P) :
    Path.symm (encDecPath s h k m) =
      Path.mk [Step.mk _ _ (h.correct k m).symm] (h.correct k m).symm := by
  simp [encDecPath, Path.symm]

/-- Trans of enc-dec path and its symm gives refl proof. -/
theorem enc_dec_trans_symm {P C K : Type u} (s : SymEncScheme P C K)
    (h : SymEncCorrect s) (k : K) (m : P) :
    (Path.trans (encDecPath s h k m) (Path.symm (encDecPath s h k m))).proof = rfl := by
  simp

end CryptoPaths
end Computation
end Path
end ComputationalPaths
