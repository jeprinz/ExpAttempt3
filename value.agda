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

-- ISSUE: should be possible for A and T to be the same, but here
-- T can't ever be in context Γ because of the way End is defined.
-- HMMM: the scenario would be x : T |- T, but then it would actually
-- have to be (x : T ⊢ weaken(T)). How can this pattern match?
-- It should somehow already know that A = weaken(T). Somehow this
-- should be the only possible case!
subValue : ∀{n m Γ' T} → (Γ : Context) → (i : InCtx {n} Γ {Γ'} T)
  → {A : Type {m} Γ} → (e : Value Γ A) → (v : Value {n} Γ' T)
    → Value (subCtx Γ i v) (subType Γ i A v)


subCtx (ConsCtx Γ T) End v = Γ
subCtx (ConsCtx Γ T) (Before i) v = ConsCtx (subCtx Γ i v) (subType Γ i T v)

weakenType : ∀ {n Γ ΓT T} → InCtx {n} Γ {ΓT} T → Type {n} Γ
-- weakenValue : ∀ {n Γ ΓT T} → (i : InCtx {n} Γ {ΓT} T) → (v : Value ΓT T)
  -- → Value Γ (weakenType i)

subType Γ inctx U v = U
subType Γ inctx (Pi p1 p2 A B) v =
  Pi p1 p2 (subType Γ inctx A v) (subType (ConsCtx Γ A) (Before inctx) B v)
subType Γ inctx (fromValue x) v = fromValue (subValue Γ inctx x v)
data UnApp where
  Var : ∀ {n Γ ΓT T} → (i : InCtx {n} Γ {ΓT} T) → UnApp Γ (weakenType i)
  App : ∀ {nA nB Γ} → {A : Type {nA} Γ} → {B : Type {nB} (ConsCtx Γ A)}
    → UnApp Γ (Pi {nA} {nB} {max nA nB} lemma2 lemma3 A B) →
    (x : Value Γ A) → UnApp Γ (subType (ConsCtx Γ A) End B x)


-- weakenTypeStep : ∀ {n Γ T} → Type {n} Γ → Type {n} (ConsCtx Γ T)
-- weakenTypeStep U = U
-- weakenTypeStep (Pi {i} {j} p1 p2 A B)
  -- = Pi p1 p2 (weakenTypeStep {i} A) {!   !}
-- weakenTypeStep (fromValue x) = {!   !}

-- weakenType End = {!   !}
-- weakenType (Before inctx) = {!   !}
weakenType = {!   !}

-- weakening a type and then substituting the end of the ctx are inverses
-- prove by pattern matching on T
subWeakenProof : ∀ {n Γ T} → (subv retv : Value {n} Γ T)
  → Value {n} Γ (subType (ConsCtx Γ T) End (weakenType End) subv)
subWeakenProof = {!   !}

subValue Γ inctx (Lambda e) v = Lambda (subValue _ (Before inctx) e v)
subValue (ConsCtx Γ' T) End {A} (fromU (Var End)) v = subWeakenProof v v
subValue (ConsCtx Γ' T) End {_} (fromU (Var (Before inctx))) v = {!   !} -- just return the var without substitution, fromU (Var inctx)
subValue .(ConsCtx _ _) (Before inctx) (fromU (Var x)) v = {!   !} -- recurse on subValue
subValue Γ inctx (fromU (App x x₁)) v = {!   !}
subValue Γ inctx (fromType T) v = fromType (subType Γ inctx T v)


-- TODO: write weaken. ITS A FUNCTION! it just transforms to a version of the
-- thing in a weaker context.

-- BIG QUESTION: is there any reason that ≤ has to be defined in the way it is?
-- what if I defined ≤ so n ≤ m for all n and m? Would anything break?
-- If not, why do I need levels?
