open import Data.Nat
-- open import Agda.Builtin.Sigma

lemma : {a : ℕ} → a ≤ a
lemma {zero} = z≤n
lemma {suc a} = s≤s lemma

max : ℕ → ℕ → ℕ -- move this elsewhere later...
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

lemma2 : {a b : ℕ} → a ≤ max a b
lemma2 {zero} {b} = z≤n
lemma2 {suc a} {zero} = lemma
lemma2 {suc a} {suc b} = s≤s lemma2

lemma3 : {a b : ℕ} → b ≤ max a b
lemma3 {zero} {b} = lemma
lemma3 {suc a} {zero} = z≤n
lemma3 {suc a} {suc b} = s≤s lemma3

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
  Pi : ∀ {i j k Γ} → (i ≤ k) → (j ≤ k) → (A : Type {i} Γ) → (B : Type {j} (ConsCtx Γ A)) → Type {k} Γ
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
subValue : ∀{n m Γ' T} → (Γ : Context) → (i : InCtx {n} Γ {Γ'} T)
  → {A : Type {m} Γ} → (e : Value Γ A) → (v : Value {n} Γ' T)
    → Value (subCtx Γ i v) (subType Γ i A v)


subCtx (ConsCtx Γ T) End v = Γ
subCtx (ConsCtx Γ T) (Before i) v = ConsCtx (subCtx Γ i v) (subType Γ i T v)



subType Γ inctx U v = U
subType Γ inctx (Pi p1 p2 A B) v =
  Pi p1 p2 (subType Γ inctx A v) (subType (ConsCtx Γ A) (Before inctx) B v)
subType Γ inctx (fromValue x) v = fromValue (subValue Γ inctx x v)
data UnApp where
  Var : ∀ {n Γ T} → InCtx {n} Γ T → UnApp Γ T
  App : ∀ {nA nB Γ} → {A : Type {nA} Γ} → {B : Type {nB} (ConsCtx Γ A)}
    → UnApp Γ (Pi {nA} {nB} {max nA nB} lemma2 lemma3 A B) →
    (x : Value Γ A) → UnApp Γ (subType (ConsCtx Γ A) End B x)

subValue Γ inctx (Lambda e) v = Lambda (subValue _ (Before inctx) e v)
subValue Γ inctx (fromU (Var x)) v = {!   !}
subValue Γ inctx (fromU (App x x₁)) v = {!   !}
subValue Γ inctx (fromType T) v = fromType (subType Γ inctx T v)


-- TODO: write weaken. ITS A FUNCTION! it just transforms to a version of the
-- thing in a weaker context.
