open import Data.Nat
-- open import Agda.Builtin.Sigma

lemma : {a : ℕ} → a ≤ a
lemma {zero} = z≤n
lemma {suc a} = s≤s lemma

max : ℕ → ℕ → ℕ -- move this elsewhere later...
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

data Context : Set  -- A list of types
data Type : {n : ℕ} → Context → Set
data InCtx : {n : ℕ} → (Γ : Context) → {Γ' : Context} → Type {n} Γ' → Set
data Value : {n : ℕ} → (Γ : Context) → (t : Type {n} Γ) → Set
data UnApp : {n : ℕ} → (Γ : Context) → (t : Type {n} Γ) → Set

data Context where -- A list of types
  ∅ : Context
  ConsCtx : ∀ {n} → (Γ : Context) →  Type {n} Γ → Context

data Type where
  U : {n : ℕ} → {Γ : Context} → Type {suc n} Γ
  Pi : ∀ {i j k Γ} → (i ≤ k) → (i ≤ k) → (A : Type {i} Γ) → (B : Type {j} (ConsCtx Γ A)) → Type {k} Γ
  fromValue : ∀ {n Γ} → Value {suc n} Γ (U {n}) → Type {n} Γ


data InCtx where
  End : ∀ {Γ n} → {T : Type {n} Γ} → InCtx {n} (ConsCtx Γ T) {Γ} T
  Before : ∀ {ΓA Γ nA nT} → {A : Type {nA} ΓA} → {T : Type {nT} Γ} → InCtx Γ A
    → InCtx {nA} (ConsCtx Γ T) {ΓA} A
    -- A is the thing thats in the context. T is on end.

data Value where
  Lambda : ∀ {n Γ A B} → Value {n} (ConsCtx {n} Γ A) B → Value Γ (Pi {n} {n} {n} lemma lemma A B)
  fromU : ∀ {n Γ T} → UnApp {n} Γ T → Value {n} Γ T
  fromType : ∀ {n Γ} → Type {n} Γ → Value {suc n} Γ (U {n})

subCtx : ∀ {n Γ' T} → (Γ : Context) → (i : InCtx {n} Γ {Γ'} T)
  → (v : Value {n} Γ' T) → Context

subType : ∀{n m Γ' T} → (Γ : Context) → (i : InCtx {n} Γ {Γ'} T)
  → (A : Type {m} Γ) → (v : Value {n} Γ' T) → Type {m} (subCtx Γ i v)
sub : ∀{n m Γ' T} → (Γ : Context) → (i : InCtx {n} Γ {Γ'} T)
  → {A : Type {m} Γ} → (e : Value Γ A) → (v : Value {n} Γ' T)
    → Value (subCtx Γ i v) (subType Γ i A v)


subCtx (ConsCtx Γ T) End v = Γ
subCtx (ConsCtx Γ T) (Before i) v = ConsCtx (subCtx Γ i v) (subType Γ i T v)
-- should be T=A and n=m
subType (ConsCtx Γ T) End U v = U
subType {n} {m} {Γ'} {T} (ConsCtx Γ X) End (Pi {i} {j} {k} p1 p2 A B) v
  = Pi {i} {j} {k} {Γ} p1 p2 (subType (ConsCtx Γ X) End A v)
    (subType {n} {j} {Γ'} {T} (ConsCtx (ConsCtx Γ X) A) (Before End) B v)
subType (ConsCtx Γ T) End (fromValue x) v = {!   !}
subType (ConsCtx Γ T) (Before i) A v = {!   !}
sub = {!   !}

data UnApp where
  Var : ∀ {n Γ T} → InCtx {n} Γ T → UnApp Γ T
  -- TODO: replace m in A with n
  -- TODO: also, should all three of those really be m?
  App : ∀ {m Γ} → {A : Type {m} Γ} → {B : Type {m} (ConsCtx Γ A)} → UnApp Γ (Pi {m} {m} {m} lemma lemma A B) →
    (x : Value Γ A) → UnApp Γ {!   !} --(subType (ConsCtx same A) End B x)

-- TODO: write weaken. ITS A FUNCTION! it just transforms to a version of the
-- thing in a weaker context.
