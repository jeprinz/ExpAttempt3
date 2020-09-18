open import Data.Nat

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
data Value : {n : ℕ} → (Γ : Context) → (t : Type {n} Γ) → Set
data UnApp : {n : ℕ} → (Γ : Context) → (t : Type {n} Γ) → Set

data Context where -- A list of types
  ∅ : Context
  ConsCtx : ∀ {n} → (Γ : Context) →  Type {n} Γ → Context

data Type where
  U : {n : ℕ} → {Γ : Context} → Type {suc n} Γ
  Pi : ∀ {i j k Γ} → (i ≤ k) → (j ≤ k) → (A : Type {i} Γ) → (B : Type {j} (ConsCtx Γ A)) → Type {k} Γ
  fromValue : ∀ {n Γ} → Value {suc n} Γ (U {n}) → Type {n} Γ

data _prefix_ : Context → Context → Set where
  same : {Γ : Context} → Γ prefix Γ
  step : {n : ℕ} → ∀{Γ' Γ T} → (p : Γ' prefix Γ) →  Γ' prefix (ConsCtx {n} Γ T)

data Value where
  Lambda : ∀ {n Γ A B} → Value {n} (ConsCtx {n} Γ A) B → Value Γ (Pi {n} {n} {n} lemma lemma A B)
  fromU : ∀ {n Γ T} → UnApp {n} Γ T → Value {n} Γ T
  fromType : ∀ {n Γ} → Type {n} Γ → Value {suc n} Γ (U {n})

subCtx : ∀ {n Γ' T} → (Γ : Context) → (ConsCtx {n} Γ' T) prefix Γ
  → (v : Value {n} Γ' T) → Context

subType : ∀{n m Γ' T} → (Γ : Context) → (i : (ConsCtx {n} Γ' T) prefix Γ)
  → (A : Type {m} Γ) → (v : Value {n} Γ' T) → Type {m} (subCtx Γ i v)

subValue : ∀{n m Γ' T} → (Γ : Context) → (i : (ConsCtx {n} Γ' T) prefix Γ)
  → {A : Type {m} Γ} → (e : Value Γ A) → (v : Value {n} Γ' T)
    → Value (subCtx Γ i v) (subType Γ i A v)

subCtx (ConsCtx Γ T) same v = Γ
subCtx (ConsCtx Γ T) (step i) v = ConsCtx (subCtx Γ i v) (subType Γ i T v)

weakenType : ∀ {n Γ ΓT T} → (ConsCtx {n} ΓT T) prefix Γ → Type {n} Γ

subType Γ icx U v = U
subType Γ icx (Pi p1 p2 A B) v =
  Pi p1 p2 (subType Γ icx A v) (subType (ConsCtx Γ A) (step icx) B v)
subType Γ icx (fromValue x) v = fromValue (subValue Γ icx x v)
data UnApp where
  Var : ∀ {n Γ ΓT T} → (i : (ConsCtx {n} ΓT T) prefix Γ) → UnApp Γ (weakenType i)
  App : ∀ {nA nB Γ} → {A : Type {nA} Γ} → {B : Type {nB} (ConsCtx Γ A)}
    → UnApp Γ (Pi {nA} {nB} {max nA nB} lemma2 lemma3 A B) →
    (x : Value Γ A) → UnApp Γ (subType (ConsCtx Γ A) same B x)

weakenCtxStep : ∀ {n Γ'} → ∀ (Γ) → (p : Γ' prefix Γ) → (toAdd : Type {n} Γ') → Context
weakenTypeStep : ∀ {n nT Γ' Γ} → (p : Γ' prefix Γ) → (toAdd : Type {n} Γ')
  → Type {nT} Γ → Type {nT} (weakenCtxStep Γ p toAdd)
weakenValueStep : ∀ {n nT Γ' Γ} → (p : Γ' prefix Γ) → (toAdd : Type {n} Γ')
  → {T : Type {nT} Γ} → Value {nT} Γ T
  → Value {nT} (weakenCtxStep Γ p toAdd) (weakenTypeStep p toAdd T)
weakenUnAppstep : ∀ {n nT Γ' Γ} → (p : Γ' prefix Γ) → (toAdd : Type {n} Γ')
  → {T : Type {nT} Γ} → UnApp {nT} Γ T
  → UnApp {nT} (weakenCtxStep Γ p toAdd) (weakenTypeStep p toAdd T)
-- TODO: plan to make this not as terrible:
-- Define InCtx {n} Γ {Γ'} T = (Γ', T, p : (ConsCtx Γ' T) prefix Γ)
-- make a function sortCtx : ∀{Γ1 Γ2 Γ} → (Γ1 prefix Γ) → (Γ2 prefix Γ)
--                              → (Γ1 prefix Γ2) + (Γ2 prefix Γ1)

data InCtx : Context → Set where
  inctx : ∀{n Γ} → ∀(Γ') → ∀(T) → (ConsCtx {n} Γ' T) prefix Γ → InCtx Γ

weakenCtxStep Γ same toAdd = ConsCtx Γ toAdd
weakenCtxStep (ConsCtx Γ T) (step p) toAdd
  = ConsCtx (weakenCtxStep Γ p toAdd) (weakenTypeStep p toAdd T)

-- TODO: next time: figure this out. Its suppose to take an InCtx
-- and a substitution and give the new version of the sub.
-- To see what type it should return, look at var case of weakenUnAppstep below.
weakenInCtxStep : ∀ {n nT Γ'p Γ} → ∀(Γ'T) → ∀(T) → (p : Γ'p prefix Γ)
  → (toAdd : Type {n} Γ'p) → (ConsCtx {nT} Γ'T T) prefix Γ
  → InCtx (weakenCtxStep Γ p toAdd)
weakenInCtxStep Γ'T T same toAdd icx = inctx Γ'T T (step icx) -- toAdd on end
weakenInCtxStep Γ'T T (step p) toAdd same
  = inctx (weakenCtxStep Γ'T p toAdd) (weakenTypeStep p toAdd T) same  -- T on end
weakenInCtxStep Γ'T T (step p) toAdd (step icx) with (weakenInCtxStep Γ'T T p toAdd icx) -- recurse
... | inctx Γ'sub Tsub pre = inctx Γ'sub Tsub (step pre)

weakenTypeStep p toAdd U = U
weakenTypeStep {n} {nT} {G'} {G} p toAdd (Pi p1 p2 A B)
  = Pi p1 p2 (weakenTypeStep p toAdd A) (weakenTypeStep (step p) toAdd B)
weakenTypeStep p toAdd (fromValue x) = fromValue (weakenValueStep p toAdd x)

weakenValueStep p toAdd (Lambda v) = Lambda (weakenValueStep (step p) toAdd v)
weakenValueStep p toAdd (fromU u) = fromU (weakenUnAppstep p toAdd u)
weakenValueStep p toAdd (fromType T) = fromType (weakenTypeStep p toAdd T)

-- TODO: subWeakenElim: P(subType(weakenTypeStep(T))) → P(T) -- I would want to use univalence here, but since I don't have it, I -- will have to do the thing where I manually code univalence for specific -- values of P. Start with P(T) = T.
weakenType {n} {(ConsCtx Γ' toAdd)} {ΓT} {T} same = weakenTypeStep same toAdd T
weakenType {n} {(ConsCtx Γ' toAdd)} {ΓT} {T} (step i) = weakenTypeStep same toAdd (weakenType i)

-- TODO: jacob: next time: write weakenInCtxStep.
weakenUnAppstep p toAdd (Var i) with weakenInCtxStep _ _ p toAdd i
... | inctx Γ' T pre = {!   !}
weakenUnAppstep p toAdd (App u v) = {!    !} -- will need subType(weakenTypeStep T) = T proof. Apply to substitute in type. might need to use trick where I manually implement univalence for a specific case.
  -- = App (weakenUnAppstep p toAdd u) (weakenValueStep p toAdd v)

subValue Γ icx (Lambda e) v = Lambda (subValue _ (step icx) e v)
subValue (ConsCtx Γ' T) same {A} (fromU (Var same)) v = {!   !}
-- prove subType(weakenTypeStep T) = T for both above and below cases.
subValue (ConsCtx Γ' T) same {_} (fromU (Var (step icx))) v = {!   !} -- just return the var without substitution, fromU (Var icx)
subValue .(ConsCtx _ _) (step icx) (fromU (Var x)) v = {!   !} -- recurse on subValue
-- TODO: shouldn't sub on App case actually use eval?
subValue Γ icx (fromU (App x x₁)) v = {!   !}
subValue Γ icx (fromType T) v = fromType (subType Γ icx T v)

-- BIG QUESTION: is there any reason that ≤ has to be defined in the way it is?
-- what if I defined ≤ so n ≤ m for all n and m? Would anything break?
-- If not, why do I need levels?
