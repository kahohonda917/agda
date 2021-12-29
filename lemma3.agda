module lemma3 where

open import DSt2
open import CPSt3

open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

subst-cont  : {var : cpstyp → Set} {τ₁ τ₂ : typ} {μα : trail} {τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  cpsSubstVal (λ x → v₁ x) v v₁′ →
  cpsSubst (λ x → k₁ x (v₁ x) (t′)) v (k₂ v₁′ t′)

subst-cont′ : {var : cpstyp → Set} {τ₁ τ₂ : typ} {μα : trail} {τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont′ {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  cpsSubst (λ x → k₁ x v₁′ (t′)) v (k₂ v₁′ t′)

mutual
  SubstV≠ : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
            {t : cpsvalue[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubstVal (λ y → t) v t

  SubstV≠ {var} {t = CPSVar x} = sVar≠
  SubstV≠ {var} {t = CPSNum n} = sNum
  SubstV≠ {var} {t = CPSFun e} = sFun λ x → Subst≠
  SubstV≠ {var} {t = CPSIdt}   = sId

  Subst≠ : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
           {t : cpsterm[ var ] τ₁} →
           {v : cpsvalue[ var ] τ₂} →
           cpsSubst (λ y → t) v t

  Subst≠ {t = CPSVal v}          = sVal SubstV≠
  Subst≠ {t = CPSApp e₁ e₂}      = sApp Subst≠ Subst≠
  Subst≠ {t = CPSLet e₁ e₂}      = sLet (λ y → Subst≠) (λ y₂ → Subst≠)
  Subst≠ {t = CPSPlus e₁ e₂}     = sPlu Subst≠ Subst≠
  Subst≠ {t = CPSIdk id e t}     = sIdk Subst≠ Subst≠
  Subst≠ {t = CPSAppend c t₁ t₂} = sApd Subst≠ Subst≠
  Subst≠ {t = CPSCons c t₁ t₂}   = sCon Subst≠ Subst≠

{-
mutual
  SubstV-id : {var : typ → Set} {τ₁ τ₂ : typ} →
              {v₁ : value[ var ] τ₁} →
              {v : value[ var ] τ₂} →
              SubstVal (λ _ → v₁) v v₁
  SubstV-id {var} {τ₁} {τ₂} {Var x} {v} = sVar≠
  SubstV-id {var} {.Nat} {τ₂} {Num n} {v} = sNum
  SubstV-id {var} {.(_ ⇒ _ ⟨ _ ⟩ _ ⟨ _ ⟩ _)} {τ₂} {Fun e₁} {v} =
    sFun λ x → Subst-id

  Subst-id : {var : typ → Set} {τ₁ τ₂ α β : typ} {μα μβ : trail} →
             {μs : trails[ μβ ] μα}
             {t : term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ] τ₂} →
             Subst (λ _ → t) v t
  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα} {t = Val x} {v} =
    sVal SubstV-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {t = App t t₁} {v} =
    sApp Subst-id Subst-id
  Subst-id {var} {.Nat} {τ₂} {α} {β} {μα} {μβ} {t = Plus t t₁} {v} =
    sPlu Subst-id Subst-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {t = Control x x₁ x₂ e} {v} =
    sCon (λ k → Subst-id)
  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα} {t = Prompt x t} {v} =
    sPro Subst-id
-}

-- schematic
schematicV : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} →
             (k : cpsvalue[ var ] (cpsT τ₁) →
             cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
             Set
schematicV {var} {τ₁} {μα = μα} k =
  (v : value[ var ∘ cpsT ] τ₁) →
  (t : cpsvalue[ var ] cpsM μα) →
  cpsSubst (λ x → k (CPSVar x) t) (cpsV v) (k (cpsV v) t)

schematic : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} →
            (k : cpsvalue[ var ] (cpsT τ₁) →
                 cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
            Set
schematic  {var} {τ₁} {μα = μα} k =
  (v : cpsvalue[ var ] (cpsT τ₁)) →
  (t : cpsvalue[ var ] cpsM μα) →
  cpsSubst (λ x → k (CPSVar x) t) v (k v t)

schematicV′ : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} →
              (k : cpsvalue[ var ] (cpsT τ₁) →
                   cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
schematicV′ {var} {τ₁} {μα = μα} k =
  (t : cpsvalue[ var ] (cpsM μα)) →
  (v₂ : cpsvalue[ var ] cpsT τ₁) →
  cpsSubst (λ x → k v₂ (CPSVar x)) t (k v₂ t)

schematicK : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} {τ : cpstyp} →
             (k : cpsvalue[ var ] τ → cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
             Set
schematicK  {var} {τ₁} {μα = μα} {τ = τ} k =
  {v : cpsvalue[ var ] τ} →
  (x : cpsvalue[ var ] (cpsT τ₁)) →
  (t : cpsvalue[ var ] cpsM μα) →
  cpsSubst (λ x₁ → k (CPSVar x₁) x t) v (k v x t)

{-
schematicK′ : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} {τ : cpstyp} →
              (k : var τ → cpsvalue[ var ] (cpsT τ₁) →
                   cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
schematicK′  {var} {τ₁} {α} {μα = μα} {τ = τ} k =
  {v : var τ} →
  (x : cpsvalue[ var ] (cpsT τ₁)) →
  (t : cpsvalue[ var ] cpsM μα) →
  {k₂ : cpsvalue[ var ] (cpsT τ₁) →
        cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
  cpsSubst (λ x₁ → k x₁ x t) (CPSVar v) (k₂ x t)
-}

mutual
  ekSubstV : {var : cpstyp → Set} {τ₁ τ : typ} →
             {v₁ : var (cpsT τ) → value[ var ∘ cpsT ] τ₁} →
             {v₁′ : value[ var ∘ cpsT ] τ₁} →
             {v : value[ var ∘ cpsT ] τ} →
             (sub : SubstVal v₁ v v₁′) →
             cpsSubstVal (λ y → cpsV {var = var} (v₁ y)) (cpsV v) (cpsV v₁′)
  ekSubstV SubstVal.sVar= = cpsSubstVal.sVar=
  ekSubstV SubstVal.sVar≠ = cpsSubstVal.sVar≠
  ekSubstV SubstVal.sNum = cpsSubstVal.sNum
  ekSubstV (sFun sub₁) =
    sFun (λ v₁ → sVal (sFun (λ k → sVal (sFun (λ t →
      ekSubst (sub₁ v₁) (λ sub₂ → sApp (sApp Subst≠ (sVal sub₂)) Subst≠))))))

  ekSubst : {var : cpstyp → Set} {τ τ₁ α β : typ}
            {μα μβ : trail} {μs : trails[ μβ ] μα} →
            {e₁ : (var ∘ cpsT) τ →
                  term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
            {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
            {v : value[ var ∘ cpsT ] τ} →
            {k₁ : var (cpsT τ) → cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
            {k₂ : cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
            {t₁ : cpsvalue[ var ] (cpsM μβ)} →
            (sub : Subst e₁ v e₂) →
            (eq : subst-cont k₁ (cpsV v) k₂) →
            cpsSubst (λ y → cpsTerm (e₁ y) (k₁ y) t₁) (cpsV v)
                     (cpsTerm e₂ k₂ t₁)

  ekSubst (sVal v) eq = eq (ekSubstV v)
  ekSubst (sApp sub₁ sub₂) eq =
    ekSubst sub₁ (λ m →
      ekSubst sub₂ (λ n →
        sApp (sApp (sApp (sVal m) (sVal n))
                   (sVal (sFun (λ x → sVal (sFun (λ x₁ → eq SubstV≠))))))
             Subst≠))
  ekSubst (sPlu sub₁ sub₂) eq =
    ekSubst sub₁ (λ m →
      ekSubst sub₂ (λ n →
        sLet (λ x → eq SubstV≠)
             (λ x → sPlu (sVal m) (sVal n))))
  ekSubst (sCon e) eq =
    sLet (λ x → ekSubst (e x) (λ v → sIdk (sVal v) Subst≠))
         (λ x → sVal (sFun (λ v → sVal (sFun λ k → sVal (sFun (λ t →
                  sLet (λ t' → eq SubstV≠) (λ t' → Subst≠)))))))
  ekSubst (sPro e) eq =
    sLet (λ v → eq SubstV≠)
         (λ v → ekSubst e (λ t → sIdk (sVal t) Subst≠))

-- to be deleted
eSubst : {var : cpstyp → Set} {τ₁ α β τ : typ} {μα μβ : trail}
         {μs : trails[ μβ ] μα} →
         {e₁ : var (cpsT τ) → term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
         {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
         {v : value[ var ∘ cpsT ] τ} →
         {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
              cpsterm[ var ] (cpsT α)} →
         {t :  cpsvalue[ var ] cpsM μβ} →
         Subst e₁ v e₂ →
         subst-cont (λ x → k) (cpsV v) k →
         cpsSubst (λ x → cpsTerm (e₁ x) k t) (cpsV v)
         (cpsTerm e₂ k t)
eSubst sub eq = ekSubst sub eq

kSubst′′ : {var : cpstyp → Set} {τ₁ α β : typ}
           {μα μβ : trail} {μs : trails[ μβ ] μα} {τ : cpstyp} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] τ} →
           {k₁ : var τ →
                 cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                 cpsterm[ var ] (cpsT α)} →
           {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                 cpsterm[ var ] (cpsT α)} →
           {t₁ : cpsvalue[ var ] (cpsM μβ)} →
           (sub-k : subst-cont k₁ v k₂) →
           cpsSubst (λ x → cpsTerm e (k₁ x) t₁) v (cpsTerm e k₂ t₁)
kSubst′′ (Val v) sub-k = sub-k SubstV≠
kSubst′′ (App e₁ e₂) sub-k =
  kSubst′′ e₁ (λ sub-v₁ →
    kSubst′′ e₂ (λ sub-v₂ →
      sApp (sApp (sApp (sVal sub-v₁) (sVal sub-v₂))
                 (sVal (sFun (λ v → sVal (sFun (λ t → sub-k SubstV≠))))))
           Subst≠))
kSubst′′ (Plus e₁ e₂) sub-k =
  kSubst′′ e₁ (λ sub-v₁ →
    kSubst′′ e₂ (λ sub-v₂ →
      sLet (λ x → sub-k SubstV≠)
           (λ n → sPlu (sVal sub-v₁) (sVal sub-v₂))))
kSubst′′ (Control id c₁ c₂ e) sub-k =
  sLet (λ x → Subst≠)
       (λ x → sVal (sFun (λ v → sVal (sFun (λ k → sVal (sFun (λ t →
                sLet (λ t' → sub-k SubstV≠)
                     (λ t' → Subst≠))))))))
kSubst′′ (Prompt id e) sub-k =
  sLet (λ x → sub-k SubstV≠)
       (λ x → Subst≠)

kSubst : {var : cpstyp → Set} {τ₁ α β : typ}
         {μα μβ : trail} {μs : trails[ μβ ] μα} {τ : cpstyp} →
         (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
         {v : cpsvalue[ var ] τ} →
         {k : cpsvalue[ var ] τ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
         {t : cpsvalue[ var ] (cpsM μβ)} →
         (sch : schematicK k) →
         cpsSubst (λ x → cpsTerm e (k (CPSVar x)) t) v
                  (cpsTerm e (k v) t)
kSubst (Val v) {t = t} sch = sch (cpsV v) t
kSubst (App e₁ e₂) sch =
  kSubst e₁ (λ v₁ t₁ →
    kSubst e₂ (λ v₂ t₂ →
      sApp (sApp Subst≠
                 (sVal (sFun λ x₁ → sVal (sFun (λ x₂ →
                   sch (CPSVar x₁) (CPSVar x₂))))))
           Subst≠))
kSubst (Plus e₁ e₂) sch =
  kSubst e₁ (λ v₁ t₁ →
    kSubst e₂ (λ v₂ t₂ →
      sLet (λ n → sch (CPSVar n) t₂)
           (λ n → Subst≠)))
kSubst (Control id c₁ c₂ e) sch =
  sLet (λ x → Subst≠)
       (λ x → sVal (sFun (λ v → sVal (sFun (λ k → sVal (sFun (λ t →
                 sLet (λ t' → sch (CPSVar v) (CPSVar t'))
                      (λ t' → Subst≠))))))))
kSubst (Prompt id e) {t = t} sch =
  sLet (λ x → sch (CPSVar x) t)
       (λ x → Subst≠)

tSubst : {var : cpstyp → Set} {τ₁ α β : typ}
         {μα μβ : trail} {μs : trails[ μβ ] μα} →
         (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
         {v : cpsvalue[ var ] (cpsM μβ)} →
         {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
              cpsterm[ var ] (cpsT α)} →
         (sch : schematicV′ k) →
         cpsSubst (λ x → cpsTerm e k (CPSVar x)) v (cpsTerm e k v)
tSubst (Val v₁) {v = v} sch = sch v (cpsV v₁)
tSubst (App e₁ e₂) sch =
  tSubst e₁ (λ t₁ v₁ →
    tSubst e₂ (λ t₂ v₂ →
      sApp Subst≠ (sVal sVar=)))
tSubst (Plus e₁ e₂) sch =
  tSubst e₁ (λ t₁ v₁ →
    tSubst e₂ (λ t₂ v₂ →
      sLet (λ n → sch t₂ (CPSVar n))
           (λ n → Subst≠)))
tSubst (Control id c₁ c₂ e) sch =
  sLet (λ x → Subst≠)
       (λ x → sVal (sFun (λ v → sVal (sFun (λ k → sVal (sFun (λ t →
                sLet (λ t' → Subst≠)
                     (λ t' → sApd (sVal sVar=) Subst≠))))))))
tSubst (Prompt id e) {v = v} sch =
  sLet (λ x → sch v (CPSVar x))
       (λ x → Subst≠)

correctCont : {var : cpstyp → Set} {τ₁ α β : typ}
              {μα μβ : trail} {μs : trails[ μβ ] μα} →
              (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
              (k₁ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                    cpsterm[ var ] (cpsT α)) →
              {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                    cpsterm[ var ] (cpsT α)} →
              {t : cpsvalue[ var ] (cpsM μβ)} →
              (sch : schematic k₁) →
              (eq : (v : value[ var ∘ cpsT ] τ₁) →
                    (t : cpsvalue[ var ] (cpsMs μs)) →
                    cpsEqual (k₁ (cpsV v) t) (k₂ (cpsV v) t)) →
              cpsEqual (cpsTerm e k₁ t) (cpsTerm e k₂ t)

correctCont (Val v) k₁ {t = t} sch eq = eq v t
correctCont {μs = μs} (App e₁ e₂) k₁ {k₂} {t} sch eq = begin
    (cpsTerm {μs = μs} (App e₁ e₂) k₁ t)
  ⟷⟨ correctCont e₁ _
        (λ v₁ t₁ → kSubst′′ e₂ (λ sub₂ →
          sApp (sApp (sApp (sVal sVar=) (sVal sub₂)) Subst≠) Subst≠))
        (λ v₁ t₁ → correctCont e₂ _
          (λ v₂ t₂ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
          (λ v₂ t₂ → eApp₁ (eApp₂ (eFun (λ x → eFun (λ k →
            eq (Var x) (CPSVar k))))))) ⟩
    (cpsTerm {μs = μs} (App e₁ e₂) k₂ t)
  ∎
correctCont {μs = μs} (Plus e₁ e₂) k₁ {k₂} {t} sch eq = begin
    (cpsTerm {μs = μs} (Plus e₁ e₂) k₁ t)
  ⟷⟨ correctCont e₁ _
        (λ v₁ t₁ → kSubst′′ e₂ (λ sub₂ →
          sLet (λ n → Subst≠) (λ n → sPlu (sVal sVar=) (sVal sub₂))))
        (λ v₁ t₁ → correctCont e₂ _
          (λ v₂ t₂ → sLet (λ n → Subst≠) (λ n → sPlu Subst≠ (sVal sVar=)))
          (λ v₂ t₂ → eLet₂ (λ n → eq (Var n) t₂))) ⟩
    (cpsTerm {μs = μs} (Plus e₁ e₂) k₂ t)
  ∎
correctCont {μs = μs} (Control {μs₁ = μs₁} id c₁ c₂ e) k₁ {k₂} {t} sch eq =
  begin
    (cpsTerm {μs = μs} (Control {μs₁ = μs₁} id c₁ c₂ e) k₁ t)
  ⟷⟨ eLet₁ (eFun (λ x → eFun (λ k → eFun (λ t' →
               eLet₂ (λ t'' → eq (Var x) (CPSVar t'')))))) ⟩
    (cpsTerm {μs = μs} (Control {μs₁ = μs₁} id c₁ c₂ e) k₂ t)
  ∎
correctCont (Prompt id e) k₁ {k₂} {t} sch eq =
  begin
    (cpsTerm (Prompt id e) k₁ t)
  ⟷⟨ eLet₂ (λ x → eq (Var x) t) ⟩
    (cpsTerm (Prompt id e) k₂ t)
  ∎

mutual
  pSubstV≠ : {var : typ → Set} {τ₁ τ₂ : typ} →
             {t : value[ var ] τ₁ } →
             {v : value[ var ] τ₂ } →
             SubstVal (λ y → t) v t
  pSubstV≠ {t = Var x} = sVar≠
  pSubstV≠ {t = Num n} = sNum
  pSubstV≠ {t = Fun e₁} = sFun (λ x → pSubst≠)

  pSubst≠ : {var : typ → Set} {τ₁ τ₂ α β : typ}
            {μα μβ : trail} {μs : trails[ μβ ] μα} →
            {t : term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
            {v : value[ var ] τ₂ } →
            Subst (λ y → t) v t
  pSubst≠ {t = Val x} = sVal pSubstV≠
  pSubst≠ {t = App t t₁} = sApp pSubst≠ pSubst≠
  pSubst≠ {t = Plus t t₁} = sPlu pSubst≠ pSubst≠
  pSubst≠ {t = Control x x₁ x₂ e} = sCon (λ k → pSubst≠)
  pSubst≠ {t = Prompt x t} = sPro pSubst≠

subst-context : {var : typ → Set} {τ α τ₁ τ₂ α' : typ}
                {μα μ₁ μ₂ : trail} {μt : trails[ μ₂ ] μ₁} →
                (con : pcontext[ var , τ ⟨ []{μα} ⟩ α ⟨ μα ⟩ α ]
                                 τ₁ ⟨ μt ⟩ τ₂ ⟨ μ₂ ⟩ α' ) →
                (v : value[ var ] τ) →
                Subst (λ x → pcontext-plug con (Val (Var x))) v
                      (pcontext-plug con (Val v))

subst-context Hole v = sVal sVar=
subst-context (Frame (App₁ e₂) con) v = sApp (subst-context con v) pSubst≠
subst-context (Frame (App₂ v₁) con) v = sApp pSubst≠ (subst-context con v)
subst-context (Frame (Plus₁ e₂) con) v = sPlu (subst-context con v) pSubst≠
subst-context (Frame (Plus₂ v₁) con) v = sPlu pSubst≠ (subst-context con v)

-- control lemma
control-lemma : {var : cpstyp → Set} {τ τ₁ τ₂' τ₅ α β {- t₁ t₂ -} : typ}
              {μ₀ {- μ₂ μ₁ -} μα μβ μα' μγ : trail}
              {μ[β]γ : trails[ μβ ] μγ} →
              {μ[α]γ : trails[ μα ] μγ} →
              {μ[β]α : trails[ μβ ] μα} →
              (p₁ : pcontext[ var ∘ cpsT , τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ]
                            τ₁ ⟨ μ[β]γ ⟩ τ₅ ⟨ μβ ⟩ β ) →
              (p₂ : pcontext[ var ∘ cpsT , τ ⟨ []{μα'} ⟩ τ₂' ⟨ μα' ⟩ τ₂' ]
                            τ₁ ⟨ μ[α]γ ⟩ τ₅ ⟨ μα ⟩ α ) →
              -- (c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
              (c₂ : compatible μβ μ₀ μα) →
              same-pcontext p₁ p₂ →
              (e : term[ var ∘ cpsT ] τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β) →
              (k₁ : cpsvalue[ var ] cpsT τ₁ → cpsvalue[ var ] cpsM μγ →
                    cpsterm[ var ] cpsT τ₅) →
              (tr : cpsvalue[ var ] cpsM μβ) →
              (sch : schematic k₁) →
              (sch' : schematicV′ k₁) →
              cpsEqual
               (cpsTerm (pcontext-plug p₁ e) k₁ tr)
               (cpsTerm {μs = μ[β]γ}
                 (App {μ[γ]β = μ[β]α}
                      (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))
                      e)
                 k₁ tr)

-- control-lemma = {!!}

--  control lemma starts
control-lemma {μ[β]α = μ[β]α} .Hole .Hole c₂ Hole e k₁ tr sch sch' =
  begin
    (cpsTerm (pcontext-plug Hole e) k₁ tr)
  ≡⟨ refl ⟩
    (cpsTerm e k₁ tr)
  ⟷⟨ correctCont e _ sch (λ v t → begin
      (k₁ (cpsV v) t)
    ⟵⟨ rBeta (sch' t (cpsV v)) ⟩
      CPSApp (CPSVal (CPSFun (λ z → k₁ (cpsV v) (CPSVar z)))) (CPSVal t)
    ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ t → sch (cpsV v) (CPSVar t))))) ⟩
      CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t''))))))
         (CPSVal (cpsV v)))
        (CPSVal t)
    ⟵⟨ rBeta (sApp Subst≠ (sVal sVar=)) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSApp
             (CPSApp
              (CPSVal
               (CPSFun
                (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t''))))))
              (CPSVal (cpsV v)))
             (CPSVal (CPSVar z)))))
        (CPSVal t)
    ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ t →
                 sApp (sApp (sVal sVar=) Subst≠) Subst≠)))) ⟩
      CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ z →
              CPSVal
              (CPSFun
               (λ z₁ →
                  CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal (cpsV v)))
                  (CPSVal (CPSVar z₁)))))))
         (CPSVal
          (CPSFun
           (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
        (CPSVal t)
    ⟵⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ t' →
          sApp (sApp Subst≠ (sVal sVar=)) Subst≠))))))) ⟩
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar x)))
                      (CPSVal (CPSVar t')))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
       (CPSVal t))
    ∎) ⟩
    (cpsTerm e
     (λ v t →
        CPSApp
        (CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ x →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar x)))
                       (CPSVal (CPSVar t')))))))))
          (CPSVal v))
         (CPSVal
          (CPSFun
           (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
        (CPSVal t))
     tr)
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]α}
     (App (Val (Fun (λ x → Val (Var x)))) e) k₁ tr)
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]α}
     (App (Val (Fun (λ x → pcontext-plug Hole (Val (Var x))))) e) k₁ tr)
  ∎

control-lemma {μ[β]γ = μ[β]γ} {μ[α]γ = μ[α]γ} ._ ._ c₂
              (Frame {μ[μ₄]μ₃ = μ[μ₄]μ₃} (App₁ e₂) {p₁} {p₂} same)
              e k₁ tr sch sch' =
  begin
    (cpsTerm {μs = μ[β]γ} (pcontext-plug (Frame (App₁ e₂) p₁) e) k₁ tr)
  ≡⟨ refl ⟩
      (cpsTerm (pcontext-plug p₁ e)
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       tr)
  ⟷⟨ control-lemma p₁ p₂ c₂ same e _ tr
        (λ v t → kSubst e₂ (λ v₂ t₂ → sApp (sApp (sApp (sVal sVar=) Subst≠)
                                                  Subst≠)
                                            Subst≠))
        (λ t v → tSubst e₂ (λ t₂ v₂ → sApp Subst≠ (sVal sVar=))) ⟩
    cpsTerm {μs = μ[μ₄]μ₃}
      (App (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x))))) e)
      (λ v₁ →
         cpsTerm e₂
         (λ v₂ t₃ →
            CPSApp
            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
             (CPSVal
              (CPSFun
               (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
            (CPSVal t₃)))
      tr
--------------------------------------------------------------------------- 1
  ⟷⟨ correctCont e _
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ v t → begin
    (CPSApp
     (CPSApp
      (CPSApp
       (CPSVal (cpsV (Fun (λ x → pcontext-plug p₂ (Val (Var x))))))
       (CPSVal (cpsV v)))
      (CPSVal
       (CPSFun
        (λ v₁ →
           CPSVal
           (CPSFun
            (λ t'' →
               cpsTerm e₂
               (λ v₂ t₃ →
                  CPSApp
                  (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                   (CPSVal
                    (CPSFun
                     (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                  (CPSVal t₃))
               (CPSVar t'')))))))
     (CPSVal t))
   ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ t →
         eSubst (subst-context p₂ v)
           (λ sub-v₁ → sApp (sApp Subst≠ (sVal sub-v₁)) Subst≠)))))))) ⟩
    CPSApp
      (CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                cpsTerm (pcontext-plug p₂ (Val v))
                (λ v₁ t'' →
                   CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v₁)) (CPSVal t''))
                (CPSVar z₁))))))
       (CPSVal
        (CPSFun
         (λ v₁ →
            CPSVal
            (CPSFun
             (λ t'' →
                cpsTerm e₂
                (λ v₂ t₃ →
                   CPSApp
                   (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                    (CPSVal
                     (CPSFun
                      (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                   (CPSVal t₃))
                (CPSVar t'')))))))
      (CPSVal t)
   ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ t →
         kSubst (pcontext-plug p₂ (Val v))
           (λ v₂ t₂ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))) ⟩
    CPSApp
      (CPSVal
       (CPSFun
        (λ z →
           cpsTerm (pcontext-plug p₂ (Val v))
           (λ z₁ z₂ →
              CPSApp
              (CPSApp
               (CPSVal
                (CPSFun
                 (λ v₁ →
                    CPSVal
                    (CPSFun
                     (λ t'' →
                        cpsTerm e₂
                        (λ v₂ t₃ →
                           CPSApp
                           (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                            (CPSVal
                             (CPSFun
                              (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                           (CPSVal t₃))
                        (CPSVar t''))))))
               (CPSVal z₁))
              (CPSVal z₂))
           (CPSVar z))))
      (CPSVal t)
   ⟶⟨ rBeta (tSubst (pcontext-plug p₂ (Val v))
          (λ t₂ v₂ → sApp Subst≠ (sVal sVar=))) ⟩
    cpsTerm (pcontext-plug p₂ (Val v))
      (λ z₁ z₂ →
         CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ v₁ →
               CPSVal
               (CPSFun
                (λ t'' →
                   cpsTerm e₂
                   (λ v₂ t₃ →
                      CPSApp
                      (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                       (CPSVal
                        (CPSFun
                         (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                      (CPSVal t₃))
                   (CPSVar t''))))))
          (CPSVal z₁))
         (CPSVal z₂))
      t
--------------------------------------------------------------------------- 2
   ⟷⟨ correctCont (pcontext-plug p₂ (Val v)) _
         (λ v₁ t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
         (λ v₁ t₁ → begin
    (CPSApp
     (CPSApp
      (CPSVal
       (CPSFun
        (λ v₂ →
           CPSVal
           (CPSFun
            (λ t'' →
               cpsTerm e₂
               (λ v₃ t₃ →
                  CPSApp
                  (CPSApp (CPSApp (CPSVal (CPSVar v₂)) (CPSVal v₃))
                   (CPSVal
                    (CPSFun
                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
                  (CPSVal t₃))
               (CPSVar t''))))))
      (CPSVal (cpsV v₁)))
     (CPSVal t₁))
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          kSubst e₂
          {k = (λ v₂ v₃ t₃ →
                  CPSApp
                  (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                   (CPSVal
                    (CPSFun
                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
                  (CPSVal t₃))}
          (λ x₁ t₄ →
            sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))))) ⟩
    (CPSApp (CPSVal
           (CPSFun
            (λ t'' →
               cpsTerm e₂
               (λ v₃ t₃ →
                  CPSApp
                  (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₃))
                   (CPSVal
                    (CPSFun
                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
                  (CPSVal t₃))
               (CPSVar t''))))
     (CPSVal t₁))
    ⟶⟨ rBeta (tSubst e₂ (λ t₄ v₂ →
          sApp Subst≠ (sVal sVar=))) ⟩
     cpsTerm e₂
       (λ v₃ t₃ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₃))
           (CPSVal
            (CPSFun
             (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
          (CPSVal t₃))
       t₁
--------------------------------------------------------------------------- 3
    ⟷⟨ correctCont e₂ _
          (λ v₂ t₂ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
          (λ v₂ t₂ → begin
    (CPSApp
     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
      (CPSVal
       (CPSFun
        (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
     (CPSVal t₂))
   ⟷⟨ eApp₁ (eApp₂ (eFun (λ x → eFun (λ x₁ → eReduce′ (rBeta
         (sch' (CPSVar x₁) (CPSVar x))))))) ⟩
    CPSApp
      (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSApp (CPSVal (CPSFun (λ z₂ → k₁ (CPSVar z) (CPSVar z₂))))
                (CPSVal (CPSVar z₁))))))))
      (CPSVal t₂)
   ⟷⟨ eApp₁ (eApp₂ (eFun (λ x → eFun (λ x₁ → eApp₁ (eReduce′ (rBeta
         (sVal (sFun (λ x₂ → sch (CPSVar x) (CPSVar x₂)))))))))) ⟩
    (CPSApp
     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
      (CPSVal
       (CPSFun
        (λ v₃ →
           CPSVal
           (CPSFun
            (λ t'' →
               CPSApp
               (CPSApp
                (CPSVal
                 (CPSFun
                  (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                (CPSVal (CPSVar v₃)))
               (CPSVal (CPSVar t''))))))))
     (CPSVal t₂))
    ∎) ⟩
--------------------------------------------------------------------------- 3
    (cpsTerm e₂
     (λ v₂ t₃ →
        CPSApp
        (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
         (CPSVal
          (CPSFun
           (λ v₃ →
              CPSVal
              (CPSFun
               (λ t'' →
                  CPSApp
                  (CPSApp
                   (CPSVal
                    (CPSFun
                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                   (CPSVal (CPSVar v₃)))
                  (CPSVal (CPSVar t''))))))))
        (CPSVal t₃))
     t₁)
    ∎) ⟩
--------------------------------------------------------------------------- 2
    cpsTerm (pcontext-plug p₂ (Val v))
      (λ z z₁ →
         cpsTerm e₂
         (λ v₂ t₃ →
            CPSApp
            (CPSApp (CPSApp (CPSVal z) (CPSVal v₂))
             (CPSVal
              (CPSFun
               (λ v₃ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp
                      (CPSApp
                       (CPSVal
                        (CPSFun
                         (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                       (CPSVal (CPSVar v₃)))
                      (CPSVal (CPSVar t''))))))))
            (CPSVal t₃))
         z₁)
      t
   ⟵⟨ rBeta (tSubst (pcontext-plug p₂ (Val v))
         (λ t₃ v₂ → tSubst e₂ (λ t₄ v₃ →
         sApp Subst≠ (sVal sVar=)))) ⟩
    CPSApp
      (CPSVal
       (CPSFun
        (λ z →
           cpsTerm (pcontext-plug p₂ (Val v))
           (λ v₁ →
              cpsTerm e₂
              (λ v₂ t₃ →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                  (CPSVal
                   (CPSFun
                    (λ v₃ →
                       CPSVal
                       (CPSFun
                        (λ t'' →
                           CPSApp
                           (CPSApp
                            (CPSVal
                             (CPSFun
                              (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                            (CPSVal (CPSVar v₃)))
                           (CPSVal (CPSVar t''))))))))
                 (CPSVal t₃)))
           (CPSVar z))))
      (CPSVal t)
   ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x →
         kSubst (pcontext-plug p₂ (Val v)) (λ x₁ t₁ →
           kSubst e₂ {k = λ x₂ v₂ t₄ →
                            CPSApp
                            (CPSApp (CPSApp (CPSVal x₁) (CPSVal v₂))
                             (CPSVal
                              (CPSFun
                               (λ v₃ →
                                  CPSVal
                                  (CPSFun
                                   (λ t'' →
                                      CPSApp (CPSApp (CPSVal x₂) (CPSVal (CPSVar v₃)))
                                      (CPSVal (CPSVar t''))))))))
                            (CPSVal t₄)}
                         (λ x₂ t₄ →
         sApp (sApp Subst≠ (sVal (sFun (λ x₃ → sVal (sFun (λ x₄ →
           sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))) Subst≠)))))) ⟩
    CPSApp
      (CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                cpsTerm (pcontext-plug p₂ (Val v))
                (λ v₁ →
                   cpsTerm e₂
                   (λ v₂ t₂ →
                      CPSApp
                      (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                       (CPSVal
                        (CPSFun
                         (λ v₃ →
                            CPSVal
                            (CPSFun
                             (λ t'' →
                                CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal (CPSVar v₃)))
                                (CPSVal (CPSVar t''))))))))
                      (CPSVal t₂)))
                (CPSVar z₁))))))
       (CPSVal
        (CPSFun
         (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
      (CPSVal t)
   ⟵⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
         eSubst (subst-context p₂ v)
           (λ x₂ → kSubst′′ e₂ (λ sub →
             sApp (sApp (sApp (sVal x₂) (sVal sub)) Subst≠) Subst≠))))))))) ⟩
    (CPSApp
     (CPSApp
      (CPSApp
       (CPSVal
        (cpsV (Fun {μs = μ[α]γ} (λ x →
                App (pcontext-plug p₂ (Val (Var x))) e₂))))
       (CPSVal (cpsV v)))
      (CPSVal
       (CPSFun
        (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
     (CPSVal t))
   ∎)⟩
--------------------------------------------------------------------------- 1
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[α]γ}
      (Val (Fun (λ x → App (pcontext-plug p₂ (Val (Var x))) e₂)))
      e)
     k₁ tr)
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[α]γ}
      (Val
       (Fun (λ x → pcontext-plug (Frame (App₁ e₂) p₂) (Val (Var x)))))
      e)
     k₁ tr)
  ∎

control-lemma {μ[β]γ = μ[β]γ} ._ ._ c₂
              (Frame {μ[μ₄]μ₃ = μ[μ₄]μ₃} (App₂ v₁) {p₁} {p₂} same)
              e k₁ tr sch sch' =
  begin
    (cpsTerm (pcontext-plug (Frame (App₂ v₁) p₁) e) k₁ tr)
  ≡⟨ refl ⟩
      (cpsTerm (pcontext-plug p₁ e)
       (λ v₂ t₃ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
          (CPSVal t₃))
       tr)
  ⟷⟨ control-lemma p₁ p₂ c₂ same e _ tr
        (λ v₂ t₂ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ t₂ v₂ → sApp Subst≠ (sVal sVar=)) ⟩
    cpsTerm {μs = μ[μ₄]μ₃}
      (App (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x))))) e)
      (λ v₂ t₃ →
         CPSApp
         (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
          (CPSVal
           (CPSFun
            (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
         (CPSVal t₃))
      tr
---------------------------------------------------------------------- 1 start
  ⟷⟨ correctCont e _
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ v t → begin
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v₂ t'' →
                         CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v₂)) (CPSVal t''))
                      (CPSVar t'))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₂ →
             CPSVal
             (CPSFun
              (λ t'' →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                  (CPSVal
                   (CPSFun
                    (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                 (CPSVal (CPSVar t''))))))))
       (CPSVal t))
   ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
         eSubst (subst-context p₂ v)
           (λ x₂ → sApp (sApp Subst≠ (sVal x₂)) Subst≠)))))))) ⟩
     CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSVal
             (CPSFun
              (λ z₁ →
                 cpsTerm (pcontext-plug p₂ (Val v))
                 (λ v₂ t'' →
                    CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v₂)) (CPSVal t''))
                 (CPSVar z₁))))))
        (CPSVal
         (CPSFun
          (λ v₂ →
             CPSVal
             (CPSFun
              (λ t'' →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                  (CPSVal
                   (CPSFun
                    (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                 (CPSVal (CPSVar t''))))))))
       (CPSVal t)
   ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
         kSubst′′ (pcontext-plug p₂ (Val v)) (λ x₁ →
           sApp (sApp (sVal sVar=) (sVal x₁)) Subst≠))))) ⟩
     CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            cpsTerm (pcontext-plug p₂ (Val v))
            (λ z₁ z₂ →
               CPSApp
               (CPSApp
                (CPSVal
                 (CPSFun
                  (λ v₂ →
                     CPSVal
                     (CPSFun
                      (λ t'' →
                         CPSApp
                         (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                          (CPSVal
                           (CPSFun
                            (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                         (CPSVal (CPSVar t'')))))))
                (CPSVal z₁))
               (CPSVal z₂))
            (CPSVar z))))
       (CPSVal t)
   ⟶⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₃ v₂ →
         sApp Subst≠ (sVal sVar=))) ⟩
     cpsTerm (pcontext-plug p₂ (Val v))
       (λ z₁ z₂ →
          CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ v₂ →
                CPSVal
                (CPSFun
                 (λ t'' →
                    CPSApp
                    (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                     (CPSVal
                      (CPSFun
                       (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                    (CPSVal (CPSVar t'')))))))
           (CPSVal z₁))
          (CPSVal z₂))
       t
---------------------------------------------------------------------- 2 start
     ⟷⟨ correctCont (pcontext-plug p₂ (Val v)) _
         (λ v₂ t₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
         (λ v₂ t₂ → begin
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₃ →
             CPSVal
             (CPSFun
              (λ t'' →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                  (CPSVal
                   (CPSFun
                    (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
                 (CPSVal (CPSVar t'')))))))
        (CPSVal (cpsV v₂)))
       (CPSVal t₂))
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ t → sApp (sApp (sApp Subst≠ (sVal sVar=))
                                                    Subst≠)
                                              Subst≠)))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSApp
             (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
              (CPSVal
               (CPSFun
                (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
             (CPSVal (CPSVar z)))))
        (CPSVal t₂)
    ⟶⟨ rBeta (sApp Subst≠ (sVal sVar=)) ⟩
      CPSApp
        (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
         (CPSVal
          (CPSFun
           (λ z → CPSVal (CPSFun (λ z₁ → k₁ (CPSVar z) (CPSVar z₁)))))))
        (CPSVal t₂)
    ⟷⟨ eApp₁ (eApp₂ (eFun (λ v → eFun (λ t → eReduce′
          (rBeta (sch' (CPSVar t) (CPSVar v))))))) ⟩
      CPSApp
        (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
         (CPSVal
          (CPSFun
           (λ z →
              CPSVal
              (CPSFun
               (λ z₁ →
                  CPSApp (CPSVal (CPSFun (λ z₂ → k₁ (CPSVar z) (CPSVar z₂))))
                  (CPSVal (CPSVar z₁))))))))
        (CPSVal t₂)
    ⟷⟨ eApp₁ (eApp₂ (eFun (λ v → eFun (λ t → eReduce′
          (rApp₁ (rBeta (sVal (sFun (λ t' →
            sch (CPSVar v) (CPSVar t')))))))))) ⟩
      (CPSApp
       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
        (CPSVal
         (CPSFun
          (λ v₃ →
             CPSVal
             (CPSFun
              (λ v₄ →
                 CPSApp
                 (CPSApp
                  (CPSVal
                   (CPSFun
                    (λ v₅ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₅) (CPSVar t''))))))
                  (CPSVal (CPSVar v₃)))
                 (CPSVal (CPSVar v₄))))))))
       (CPSVal t₂))
    ∎) ⟩
---------------------------------------------------------------------- 2 end
     cpsTerm (pcontext-plug p₂ (Val v))
       (λ z z₁ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal z))
           (CPSVal
            (CPSFun
             (λ v₂ →
                CPSVal
                (CPSFun
                 (λ v₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ v₅ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₅) (CPSVar t''))))))
                     (CPSVal (CPSVar v₂)))
                    (CPSVal (CPSVar v₃))))))))
          (CPSVal z₁))
       t
   ⟵⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₃ v₂ →
         sApp Subst≠ (sVal sVar=))) ⟩
     CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            cpsTerm (pcontext-plug p₂ (Val v))
            (λ z₁ z₂ →
               CPSApp
               (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal z₁))
                (CPSVal
                 (CPSFun
                  (λ v₂ →
                     CPSVal
                     (CPSFun
                      (λ v₃ →
                         CPSApp
                         (CPSApp
                          (CPSVal
                           (CPSFun
                            (λ v₅ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₅) (CPSVar t''))))))
                          (CPSVal (CPSVar v₂)))
                         (CPSVal (CPSVar v₃))))))))
               (CPSVal z₂))
            (CPSVar z))))
       (CPSVal t)
   ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x →
         kSubst′′ (pcontext-plug p₂ (Val v)) (λ sub →
           sApp (sApp (sApp Subst≠ (sVal sub)) (sVal (sFun (λ v →
             sVal (sFun (λ t →
               sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))) Subst≠))))) ⟩
     CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSVal
             (CPSFun
              (λ z₁ →
                 cpsTerm (pcontext-plug p₂ (Val v))
                 (λ z₂ z₃ →
                    CPSApp
                    (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal z₂))
                     (CPSVal
                      (CPSFun
                       (λ v₃ →
                          CPSVal
                          (CPSFun
                           (λ t'' →
                              CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal (CPSVar v₃)))
                              (CPSVal (CPSVar t''))))))))
                    (CPSVal z₃))
                 (CPSVar z₁))))))
        (CPSVal
         (CPSFun
          (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
       (CPSVal t)
   ⟵⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ x →
         ekSubst (subst-context p₂ v) (λ sub →
           sApp (sApp (sApp Subst≠ (sVal sub)) Subst≠) Subst≠)))))))) ⟩
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v₂ t₃ →
                         CPSApp
                         (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                          (CPSVal
                           (CPSFun
                            (λ v₃ →
                               CPSVal
                               (CPSFun
                                (λ t'' →
                                   CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar v₃)))
                                   (CPSVal (CPSVar t''))))))))
                         (CPSVal t₃))
                      (CPSVar t'))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
       (CPSVal t))
     ∎) ⟩
---------------------------------------------------------------------- 1 end
      cpsTerm e
      (λ z z₁ →
         CPSApp
         (CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ x →
                CPSVal
                (CPSFun
                 (λ k' →
                    CPSVal
                    (CPSFun
                     (λ t' →
                        cpsTerm (pcontext-plug p₂ (Val (Var x)))
                        (λ v₂ t₃ →
                           CPSApp
                           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                            (CPSVal
                             (CPSFun
                              (λ v →
                                 CPSVal
                                 (CPSFun
                                  (λ t'' →
                                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar v)))
                                     (CPSVal (CPSVar t''))))))))
                           (CPSVal t₃))
                        (CPSVar t'))))))))
           (CPSVal z))
          (CPSVal
           (CPSFun
            (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
         (CPSVal z₁))
      tr
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[β]γ}
      (Val
       (Fun (λ x → App (Val v₁) (pcontext-plug p₂ (Val (Var x))))))
      e)
     k₁ tr)
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]γ}
     (App
      (Val
       (Fun (λ x → pcontext-plug (Frame (App₂ v₁) p₂) (Val (Var x)))))
      e)
     k₁ tr)
  ∎

control-lemma {μ[β]γ = μ[β]γ} {μ[α]γ} ._ ._ c₂
              (Frame (Plus₁ e₂) {p₁} {p₂} same) e k₁ tr sch sch' =
  begin
    (cpsTerm {μs = μ[β]γ}
             (pcontext-plug (Frame (Plus₁ e₂) p₁) e) k₁ tr)
  ⟷⟨ control-lemma p₁ p₂ c₂ same e _ tr
         (λ v₂ t₂ → kSubst′′ e₂ (λ sub →
           sLet (λ n → Subst≠) (λ n → sPlu (sVal sVar=) (sVal sub))))
         (λ t₂ v₂ → tSubst e₂ (λ t₃ v₃ →
           sLet (λ n → sch' t₃ (CPSVar n)) (λ n → Subst≠))) ⟩
      cpsTerm e
      (λ v₂ t₃ →
         CPSApp
         (CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ x →
                CPSVal
                (CPSFun
                 (λ k' →
                    CPSVal
                    (CPSFun
                     (λ t' →
                        cpsTerm (pcontext-plug p₂ (Val (Var x)))
                        (λ v t'' →
                           CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                        (CPSVar t'))))))))
           (CPSVal v₂))
          (CPSVal
           (CPSFun
            (λ v →
               CPSVal
               (CPSFun
                (λ t'' →
                   cpsTerm e₂
                   (λ v₃ t₄ →
                      CPSLet (CPSPlus (CPSVal (CPSVar v)) (CPSVal v₃))
                      (λ v₁ → k₁ (CPSVar v₁) t₄))
                   (CPSVar t'')))))))
         (CPSVal t₃))
      tr
---------------------------------------------------------------------- 1 start
  ⟷⟨ correctCont e _
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ v t → begin
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v₁ t'' →
                         CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v₁)) (CPSVal t''))
                      (CPSVar t'))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₁ →
             CPSVal
             (CPSFun
              (λ t'' →
                 cpsTerm e₂
                 (λ v₃ t₅ →
                    CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₃))
                    (λ v₂ → k₁ (CPSVar v₂) t₅))
                 (CPSVar t'')))))))
       (CPSVal t))
    ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
          ekSubst (subst-context p₂ v) (λ x₂ →
            sApp (sApp Subst≠ (sVal x₂)) Subst≠)))))))) ⟩
      CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ z →
              CPSVal
              (CPSFun
               (λ z₁ →
                  cpsTerm (pcontext-plug p₂ (Val v))
                  (λ z₂ z₃ →
                     CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal z₂)) (CPSVal z₃))
                  (CPSVar z₁))))))
         (CPSVal
          (CPSFun
           (λ v₁ →
              CPSVal
              (CPSFun
               (λ t'' →
                  cpsTerm e₂
                  (λ v₃ t₅ →
                     CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₃))
                     (λ v₂ → k₁ (CPSVar v₂) t₅))
                  (CPSVar t'')))))))
        (CPSVal t)
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          kSubst′′ (pcontext-plug p₂ (Val v)) (λ x₁ →
            sApp (sApp (sVal sVar=) (sVal x₁)) Subst≠))))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             cpsTerm (pcontext-plug p₂ (Val v))
             (λ z₁ z₂ →
                CPSApp
                (CPSApp
                 (CPSVal
                  (CPSFun
                   (λ v₁ →
                      CPSVal
                      (CPSFun
                       (λ t'' →
                          cpsTerm e₂
                          (λ v₃ t₅ →
                             CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₃))
                             (λ v₂ → k₁ (CPSVar v₂) t₅))
                          (CPSVar t''))))))
                 (CPSVal z₁))
                (CPSVal z₂))
             (CPSVar z))))
        (CPSVal t)
    ⟶⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₂ v₂ →
          sApp Subst≠ (sVal sVar=))) ⟩
      cpsTerm (pcontext-plug p₂ (Val v))
        (λ z₁ z₂ →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal
                 (CPSFun
                  (λ t'' →
                     cpsTerm e₂
                     (λ v₃ t₅ →
                        CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₃))
                        (λ v₂ → k₁ (CPSVar v₂) t₅))
                     (CPSVar t''))))))
            (CPSVal z₁))
           (CPSVal z₂))
        t
---------------------------------------------------------------------- 2 start
    ⟷⟨ correctCont (pcontext-plug p₂ (Val v)) _
        (λ v₁ t₃ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v₁ t₃ → begin
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₂ →
             CPSVal
             (CPSFun
              (λ t'' →
                 cpsTerm e₂
                 (λ v₃ t₅ →
                    CPSLet (CPSPlus (CPSVal (CPSVar v₂)) (CPSVal v₃))
                    (λ v₄ → k₁ (CPSVar v₄) t₅))
                 (CPSVar t''))))))
        (CPSVal (cpsV v₁)))
       (CPSVal t₃))
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          kSubst′′ e₂ (λ x₁ →
            sLet (λ x₂ → Subst≠) (λ x₂ → sPlu (sVal sVar=) (sVal x₁))))))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             cpsTerm e₂
             (λ z₁ z₂ →
                CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal z₁))
                (λ v₂ → k₁ (CPSVar v₂) z₂))
             (CPSVar z))))
        (CPSVal t₃)
    ⟶⟨ rBeta (tSubst e₂ (λ t₄ v₂ →
          sLet (λ x → sch' t₄ (CPSVar x)) (λ x → Subst≠))) ⟩
      cpsTerm e₂
        (λ z₁ z₂ →
           CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal z₁))
           (λ v₂ → k₁ (CPSVar v₂) z₂))
        t₃
---------------------------------------------------------------------- 3 start
    ⟷⟨ correctCont e₂ _
         (λ v₂ t₁ → sLet (λ x → Subst≠) (λ x → sPlu Subst≠ (sVal sVar=)))
         (λ v₂ t₁ → eLet₂ (λ x → begin
      k₁ (CPSVar x) t₁
    ⟵⟨ rBeta (sch' t₁ (CPSVar x)) ⟩
      CPSApp (CPSVal (CPSFun (λ z → k₁ (CPSVar x) (CPSVar z))))
        (CPSVal t₁)
    ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → sch (CPSVar x) (CPSVar x₁))))) ⟩
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₅ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₅) (CPSVar t''))))))
        (CPSVal (CPSVar x)))
       (CPSVal t₁))
    ∎)) ⟩
---------------------------------------------------------------------- 3 end
      (cpsTerm e₂
       (λ v₂ v₃ →
          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
          (λ v₄ →
             CPSApp
             (CPSApp
              (CPSVal
               (CPSFun
                (λ v₅ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₅) (CPSVar t''))))))
              (CPSVal (CPSVar v₄)))
             (CPSVal v₃)))
       t₃)
    ∎) ⟩
---------------------------------------------------------------------- 2 end
      cpsTerm (pcontext-plug p₂ (Val v))
        (λ z →
           cpsTerm e₂
           (λ v₁ v₂ →
              CPSLet (CPSPlus (CPSVal z) (CPSVal v₁))
              (λ v₃ →
                 CPSApp
                 (CPSApp
                  (CPSVal
                   (CPSFun
                    (λ v₄ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₄) (CPSVar t''))))))
                  (CPSVal (CPSVar v₃)))
                 (CPSVal v₂))))
        t
    ⟵⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₄ v₂ →
          tSubst e₂ (λ t₅ v₃ →
            sLet (λ x → sApp Subst≠ (sVal sVar=)) (λ x → Subst≠)))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             cpsTerm (pcontext-plug p₂ (Val v))
             (λ z₁ z₂ →
                cpsTerm e₂
                (λ v₁ v₂ →
                   CPSLet (CPSPlus (CPSVal z₁) (CPSVal v₁))
                   (λ v₃ →
                      CPSApp
                      (CPSApp
                       (CPSVal
                        (CPSFun
                         (λ v₄ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₄) (CPSVar t''))))))
                       (CPSVal (CPSVar v₃)))
                      (CPSVal v₂)))
                z₂)
             (CPSVar z))))
        (CPSVal t)
    ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          kSubst′′ (pcontext-plug p₂ (Val v)) (λ x₁ →
            kSubst′′ e₂ (λ x₂ →
              sLet (λ x₃ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)
                   (λ x₃ → sPlu (sVal x₁) (sVal x₂)))))))) ⟩
      CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ z →
              CPSVal
              (CPSFun
               (λ z₁ →
                  cpsTerm (pcontext-plug p₂ (Val v))
                  (λ z₂ z₃ →
                     cpsTerm e₂
                     (λ v₁ v₂ →
                        CPSLet (CPSPlus (CPSVal z₂) (CPSVal v₁))
                        (λ v₃ →
                           CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal (CPSVar v₃)))
                           (CPSVal v₂)))
                     z₃)
                  (CPSVar z₁))))))
         (CPSVal
          (CPSFun
           (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
        (CPSVal t)
    ⟵⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ t →
          ekSubst (subst-context p₂ v) (λ x₂ →
            kSubst′′ e₂ (λ x₃ →
              sLet (λ x → Subst≠) (λ x → sPlu (sVal x₂) (sVal x₃))))))))))) ⟩
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v₁ →
                         cpsTerm e₂
                         (λ v₂ t₂ →
                            CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                            (λ v₃ →
                               CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar v₃)))
                               (CPSVal t₂))))
                      (CPSVar t'))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
       (CPSVal t))
    ∎) ⟩
---------------------------------------------------------------------- 1 end
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[α]γ}
      (Val
       (Fun (λ x → pcontext-plug (Frame (Plus₁ e₂) p₂) (Val (Var x)))))
      e)
     k₁ tr)
  ∎

control-lemma {μ[β]γ = μ[β]γ} {μ[α]γ} ._ ._ c₂
              (Frame (Plus₂ v₁) {p₁} {p₂} same) e k₁ tr sch sch' =
  begin
    (cpsTerm {μs = μ[β]γ}
             (pcontext-plug (Frame (Plus₂ v₁) p₁) e) k₁ tr)
  ⟷⟨ control-lemma p₁ p₂ c₂ same e _ tr
        (λ v₂ t₂ → sLet (λ x → Subst≠) (λ x → sPlu Subst≠ (sVal sVar=)))
        (λ t₂ v₂ → sLet (λ x → sch' t₂ (CPSVar x)) (λ x → Subst≠)) ⟩
    cpsTerm {μs = μ[β]γ}
      (App (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x))))) e)
      (λ v₂ t₂ →
         CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
         (λ v → k₁ (CPSVar v) t₂))
      tr
---------------------------------------------------------------------- 1 start
  ⟷⟨ correctCont e _
      (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
      (λ v t → begin
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v₂ t'' →
                         CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v₂)) (CPSVal t''))
                      (CPSVar t'))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₂ →
             CPSVal
             (CPSFun
              (λ t'' →
                 CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                 (λ v₃ → k₁ (CPSVar v₃) (CPSVar t''))))))))
       (CPSVal t))
    ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ t →
          ekSubst (subst-context p₂ v) (λ sub →
            sApp (sApp Subst≠ (sVal sub)) Subst≠)))))))) ⟩
      CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ z →
              CPSVal
              (CPSFun
               (λ z₁ →
                  cpsTerm (pcontext-plug p₂ (Val v))
                  (λ z₂ z₃ →
                     CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal z₂)) (CPSVal z₃))
                  (CPSVar z₁))))))
         (CPSVal
          (CPSFun
           (λ v₂ →
              CPSVal
              (CPSFun
               (λ t'' →
                  CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                  (λ v₃ → k₁ (CPSVar v₃) (CPSVar t''))))))))
        (CPSVal t)
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ t →
          kSubst′′ (pcontext-plug p₂ (Val v)) (λ x →
            sApp (sApp (sVal sVar=) (sVal x)) Subst≠))))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             cpsTerm (pcontext-plug p₂ (Val v))
             (λ z₁ z₂ →
                CPSApp
                (CPSApp
                 (CPSVal
                  (CPSFun
                   (λ v₂ →
                      CPSVal
                      (CPSFun
                       (λ t'' →
                          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                          (λ v₃ → k₁ (CPSVar v₃) (CPSVar t'')))))))
                 (CPSVal z₁))
                (CPSVal z₂))
             (CPSVar z))))
        (CPSVal t)
    ⟶⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₃ v₂ →
          sApp Subst≠ (sVal sVar=))) ⟩
      cpsTerm (pcontext-plug p₂ (Val v))
        (λ z z₁ →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₂ →
                 CPSVal
                 (CPSFun
                  (λ t'' →
                     CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                     (λ v₃ → k₁ (CPSVar v₃) (CPSVar t'')))))))
            (CPSVal z))
           (CPSVal z₁))
        t
---------------------------------------------------------------------- 2 start
    ⟷⟨ correctCont (pcontext-plug p₂ (Val v)) _
          (λ v₂ t₃ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
          (λ v₂ t₃ → begin
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₃ →
             CPSVal
             (CPSFun
              (λ t'' →
                 CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                 (λ v₄ → k₁ (CPSVar v₄) (CPSVar t'')))))))
        (CPSVal (cpsV v₂)))
       (CPSVal t₃))
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          sLet (λ x₁ → Subst≠) (λ x₁ → sPlu Subst≠ (sVal sVar=)))))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
             (λ z₁ → k₁ (CPSVar z₁) (CPSVar z)))))
        (CPSVal t₃)
    ⟶⟨ rBeta (sLet (λ x → sch' t₃ (CPSVar x)) (λ x → Subst≠)) ⟩
      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
        (λ z → k₁ (CPSVar z) t₃)
---------------------------------------------------------------------- 3 start
    ⟷⟨ eLet₂ (λ x → begin
      k₁ (CPSVar x) t₃
    ⟵⟨ rBeta (sch' t₃ (CPSVar x)) ⟩
      CPSApp (CPSVal (CPSFun (λ z → k₁ (CPSVar x) (CPSVar z))))
        (CPSVal t₃)
    ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → sch (CPSVar x) (CPSVar x₁))))) ⟩
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₄ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₄) (CPSVar t''))))))
        (CPSVal (CPSVar x)))
       (CPSVal t₃))
    ∎) ⟩
---------------------------------------------------------------------- 3 end
      (CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
       (λ v₃ →
          CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ v₄ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₄) (CPSVar t''))))))
           (CPSVal (CPSVar v₃)))
          (CPSVal t₃)))
    ∎) ⟩
---------------------------------------------------------------------- 2 end
      cpsTerm (pcontext-plug p₂ (Val v))
        (λ z z₁ →
           CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal z))
           (λ v₂ →
              CPSApp
              (CPSApp
               (CPSVal
                (CPSFun
                 (λ v₃ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₃) (CPSVar t''))))))
               (CPSVal (CPSVar v₂)))
              (CPSVal z₁)))
        t
    ⟵⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₃ v₂ →
          sLet (λ x → sApp Subst≠ (sVal sVar=)) (λ x → Subst≠))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             cpsTerm (pcontext-plug p₂ (Val v))
             (λ z₁ z₂ →
                CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal z₁))
                (λ v₂ →
                   CPSApp
                   (CPSApp
                    (CPSVal
                     (CPSFun
                      (λ v₃ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₃) (CPSVar t''))))))
                    (CPSVal (CPSVar v₂)))
                   (CPSVal z₂)))
             (CPSVar z))))
        (CPSVal t)
    ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          kSubst′′ (pcontext-plug p₂ (Val v)) (λ x₁ →
            sLet (λ x₂ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)
                 (λ x₂ → sPlu Subst≠ (sVal x₁))))))) ⟩
      CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ z →
              CPSVal
              (CPSFun
               (λ z₁ →
                  cpsTerm (pcontext-plug p₂ (Val v))
                  (λ z₂ z₃ →
                     CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal z₂))
                     (λ v₂ →
                        CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal (CPSVar v₂)))
                        (CPSVal z₃)))
                  (CPSVar z₁))))))
         (CPSVal
          (CPSFun
           (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
        (CPSVal t)
    ⟵⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ t →
          ekSubst (subst-context p₂ v) (λ x →
            sLet (λ x₁ → Subst≠) λ x₁ → sPlu Subst≠ (sVal x))))))))) ⟩
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v₂ t₃ →
                         CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                         (λ v₃ →
                            CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar v₃)))
                            (CPSVal t₃)))
                      (CPSVar t'))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
       (CPSVal t))
    ∎)⟩
---------------------------------------------------------------------- 1 end
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[α]γ}
      (Val
       (Fun (λ x → pcontext-plug (Frame (Plus₂ v₁) p₂) (Val (Var x)))))
      e)
     k₁ tr)
  ∎

-- end of control lemma

{-

cons-assoc-2 : {var : cpstyp → Set} {τ α τ' α' τ₁ α₁ τ₂ α₂ : typ}
               {μk μt μkt μ μ' μ₀ : trail}
               (k : cpsvalue[ var ] cpsM (τ₂ ⇒ α₂ , μk))
               (t : cpsvalue[ var ] cpsM (τ₁ ⇒ α₁ , μt))
               (kt : cpsvalue[ var ] cpsM μkt)
               (c₁ : compatible (τ₂ ⇒ α₂ , μk) (τ₁ ⇒ α₁ , μt)
                                (τ ⇒ α , μ))
               (c₂ : compatible (τ ⇒ α , μ) μkt (τ' ⇒ α' , μ'))
               (c₁' : compatible (τ₁ ⇒ α₁ , μt) μkt μ₀)
               (c₂' : compatible (τ₂ ⇒ α₂ , μk) μ₀ (τ' ⇒ α' , μ')) →
               cpsreduce (CPSVal (CPSCons c₂ (CPSCons c₁ k t) kt))
                         (CPSVal (CPSCons c₂' k (CPSCons c₁' t kt)))

cons-assoc-2 {var} {τ} {α} {τ'} {α'} {τ₁} {α₁} {τ₂} {α₂} {μk} {μt} {∙} {μ} {μ'} {μ₀} k t kt (refl , refl , c₁) refl refl (refl , refl , c₂') rewrite compatible-equal c₁ c₂' = begin
  (CPSVal (CPSCons refl (CPSCons (refl , refl , c₂') k t) kt))
  ⟶⟨ rConsid₂ ⟩
  CPSVal (CPSCons (refl , refl , c₂') k t)
  ⟵⟨ rCon₂ rConsid₂ ⟩
  (CPSVal (CPSCons (refl , refl , c₂') k (CPSCons refl t kt)))
  ∎

cons-assoc-2 {var} {τ} {α} {.τ} {.α} {τ₁} {α₁} {.τ} {.α} {.(τ₁ ⇒ α₁ , ∙)} {.(τ₃ ⇒ τ'' , μkt)} {τ₃ ⇒ τ'' , μkt} {.(τ₃ ⇒ τ'' , μkt)} {∙} {τ₁ ⇒ α₁ , ∙} k t kt (refl , refl , refl , refl , refl) (refl , refl , refl) (refl , refl , refl) (refl , refl , refl) = begin
  (CPSVal
       (CPSCons (refl , refl , refl)
        (CPSCons (refl , refl , refl , refl , refl) k t) kt))
  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , refl)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons (refl , refl , refl) t (CPSVar t')))))))
     kt)
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v₁)))
                      (CPSVal (CPSCons (refl , refl , refl) t (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons refl kt (CPSVar t')))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
                 (CPSVal (CPSCons (refl , refl , refl) t (CPSVar z₂))))))
            (CPSVal (CPSCons refl kt (CPSVar z₁)))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
            (CPSVal
             (CPSCons (refl , refl , refl) t (CPSCons refl kt (CPSVar z₁))))))))
  ⟵⟨ rFun (λ x → rFun (λ x₁ → rApp₂ (cons-assoc-2 t kt (CPSVar x₁) (refl , refl , refl) refl refl (refl , refl , refl)))) ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
            (CPSVal
             (CPSCons refl (CPSCons (refl , refl , refl) t kt) (CPSVar t')))))))
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , refl) k
        (CPSCons (refl , refl , refl) t kt)))
  ∎
cons-assoc-2 {var} {τ} {α} {.τ} {.α} {τ₁} {α₁} {.τ} {.α} {.(τ₁ ⇒ α₁ , (τ₂ ⇒ τ' , μ₀))} {τ₄ ⇒ τ''' , μt} {.τ₄ ⇒ .τ''' , μkt} {.(τ₄ ⇒ τ''' , μkt)} {∙} {τ₁ ⇒ α₁ , (τ₂ ⇒ τ' , μ₀)} k t kt (refl , refl , refl , refl , refl , refl , snd) (refl , refl , refl) (refl , refl , refl , refl , snd₁) (refl , refl , refl) = begin
  (CPSVal
       (CPSCons (refl , refl , refl)
        (CPSCons (refl , refl , refl , refl , refl , refl , snd) k t) kt))
  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , refl)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons (refl , (refl , (refl , (refl , snd)))) t (CPSVar t')))))))
     kt)
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v₁)))
                      (CPSVal
                       (CPSCons (refl , refl , refl , refl , snd) t (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons refl kt (CPSVar t')))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
                 (CPSVal
                  (CPSCons (refl , refl , refl , refl , snd) t (CPSVar z₂))))))
            (CPSVal (CPSCons refl kt (CPSVar z₁)))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
            (CPSVal
             (CPSCons (refl , refl , refl , refl , snd) t
              (CPSCons refl kt (CPSVar z₁))))))))
  ⟵⟨ rFun (λ x → rFun (λ x₁ → rApp₂ (cons-assoc-2 t kt (CPSVar x₁) (refl , refl , refl , refl , snd₁)
                                           refl refl (refl , (refl , (refl , (refl , snd))))))) ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
            (CPSVal
             (CPSCons refl (CPSCons (refl , refl , refl , refl , snd₁) t kt)
              (CPSVar t')))))))
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , refl) k
        (CPSCons (refl , refl , refl , refl , snd₁) t kt)))
  ∎
    -- (CPSVal
    --                (CPSCons c₂
    --                  (CPSCons c₁ k t) kt))
    --              (CPSVal
    --                (CPSCons c₂' k
    --                  (CPSCons c₁' t kt)))
cons-assoc-2 {var} {τ} {α} {.τ} {.α} {τ₁} {α₁} {.τ} {.α} {τ₅ ⇒ τ'''' , μk} {μt} {τ₃ ⇒ τ'' , μkt} {τ₄ ⇒ τ''' , μ} {τ₂ ⇒ τ' , μ'} {τ₁ ⇒ α₁ , ∙} k t kt (refl , refl , refl , refl , c₁) (refl , refl , refl , refl , c₂) (refl , refl , refl) (refl , refl , refl , refl , c₂') = begin
  (CPSVal
       (CPSCons (refl , refl , refl , refl , c₂)
        (CPSCons (refl , refl , refl , refl , c₁) k t) kt))
  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , refl , refl , c₂)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons (refl , (refl , c₁)) t (CPSVar t')))))))
     kt)
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v₁)))
                      (CPSVal (CPSCons (refl , refl , c₁) t (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons (refl , (refl , c₂)) kt (CPSVar t')))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
                 (CPSVal (CPSCons (refl , refl , c₁) t (CPSVar z₂))))))
            (CPSVal (CPSCons (refl , refl , c₂) kt (CPSVar z₁)))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
            (CPSVal
             (CPSCons (refl , refl , c₁) t
              (CPSCons (refl , refl , c₂) kt (CPSVar z₁))))))))
  ⟵⟨ rFun (λ x → rFun (λ x₁ → rApp₂ (cons-assoc-2 t kt (CPSVar x₁) (refl , refl , refl)
                                           (refl , refl , c₂') (refl , (refl , c₂)) (refl , (refl , c₁))))) ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
            (CPSVal
             (CPSCons (refl , (refl , c₂')) (CPSCons (refl , refl , refl) t kt) (CPSVar t')))))))
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , refl , refl , c₂') k
        (CPSCons (refl , refl , refl) t kt)))
  ∎
cons-assoc-2 {var} {τ} {α} {.τ} {.α} {τ₁} {α₁} {.τ} {.α} {τ₅ ⇒ τ'''' , μk} {μt} {τ₃ ⇒ τ'' , μkt} {τ₇ ⇒ τ'''''' , μ} {τ₂ ⇒ τ' , μ'} {τ₁ ⇒ α₁ , (τ₄ ⇒ τ''' , μ₀)} k t kt (refl , refl , refl , refl , c₁) (refl , refl , refl , refl , c₂) (refl , refl , c₁') (refl , refl , refl , refl , c₂') = begin
  (CPSVal
       (CPSCons (refl , refl , refl , refl , c₂)
        (CPSCons (refl , refl , refl , refl , c₁) k t) kt))
  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , refl , refl , c₂)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons (refl , (refl , c₁)) t (CPSVar t')))))))
     kt)
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v₁)))
                      (CPSVal (CPSCons (refl , refl , c₁) t (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons (refl , (refl , c₂)) kt (CPSVar t')))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
                 (CPSVal (CPSCons (refl , refl , c₁) t (CPSVar z₂))))))
            (CPSVal (CPSCons (refl , refl , c₂) kt (CPSVar z₁)))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
            (CPSVal
             (CPSCons (refl , refl , c₁) t
              (CPSCons (refl , refl , c₂) kt (CPSVar z₁))))))))
  ⟵⟨ rFun (λ x → rFun (λ x₁ → rApp₂ (cons-assoc-2 t kt (CPSVar x₁) (refl , refl , c₁')
                                           (refl , refl , c₂') (refl , (refl , c₂)) (refl , (refl , c₁))))) ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
            (CPSVal
             (CPSCons (refl , (refl , c₂')) (CPSCons (refl , refl , c₁') t kt) (CPSVar t')))))))
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , refl , refl , c₂') k
        (CPSCons (refl , refl , c₁') t kt)))
  ∎

--------------------------------------------------------------------------------------------------------------------------
assoc : ∀ {var : cpstyp → Set} {τ α : typ} {μα μβ μ₀ : trail}
       {μ[β]α : trails[ μβ ] μα}
       {c : compatible (τ ⇒ α , μα) μβ μβ}
       {c' : compatible (τ ⇒ α , μα) μα μα}
       {c₂ : compatible μβ μ₀ μα}
       (k : var (cpsT τ ⇛ (cpsMs μ[β]α ⇛ cpsT α)))
       (t : cpsvalue[ var ] cpsM μβ)
       (k't' : cpsvalue[ var ] cpsM μ₀) →
        cpsreduce
        (CPSVal (CPSAppend c₂ (CPSCons c (CPSVar k) t) k't'))
        (CPSVal (CPSCons c' (CPSVar k) (CPSAppend c₂ t k't')))

assoc {var} {τ} {α} {τ₁ ⇒ τ' , μα} {τ₂ ⇒ τ'' , μβ} {∙} {μ[β]α} {refl , refl , c} {refl , refl , c'} {refl} k t k't' rewrite compatible-equal c c' = begin
  (CPSVal
       (CPSAppend refl (CPSCons (refl , refl , c') (CPSVar k) t) k't'))
  ⟶⟨ rApdt ⟩
  CPSVal (CPSCons refl (CPSCons (refl , refl , c') (CPSVar k) t) k't')
  ⟶⟨ rConsid₂ ⟩
  CPSVal (CPSCons (refl , refl , c') (CPSVar k) t)
  ⟵⟨ rCon₂ rConsid₂ ⟩
  CPSVal
    (CPSCons (refl , refl , c') (CPSVar k) (CPSCons refl t k't'))
  ⟵⟨ rCon₂ rApdt ⟩
  (CPSVal
       (CPSCons (refl , refl , c') (CPSVar k) (CPSAppend refl t k't')))
  ∎
assoc {var} {τ} {α} {τ₁ ⇒ τ' , μα} {τ₂ ⇒ τ'' , μβ} {τ₃ ⇒ τ''' , μ₀} {μ[β]α} {refl , refl , c} {refl , refl , c'} {refl , refl , c₂} k t k't' = begin
  (CPSVal
       (CPSAppend (refl , refl , c₂)
        (CPSCons (refl , refl , c) (CPSVar k) t) k't'))
  ⟶⟨ rApdt ⟩
  CPSVal
    (CPSCons (refl , refl , c₂)
     (CPSCons (refl , refl , c) (CPSVar k) t) k't')
  ⟶⟨ cons-assoc-2 (CPSVar k) t k't' (refl , refl , c) (refl , refl , c₂)
       (refl , refl , c₂) (refl , refl , c') ⟩
  CPSVal
    (CPSCons (refl , refl , c') (CPSVar k)
     (CPSCons (refl , refl , c₂) t k't'))
  ⟵⟨ rCon₂ rApdt ⟩
  (CPSVal
       (CPSCons (refl , refl , c') (CPSVar k)
        (CPSAppend (refl , refl , c₂) t k't')))
  ∎
-}

--9/22--------------------------------------------------------------------
aux₄-s : {var : cpstyp → Set} {τ α β : typ} {μα μβ : trail}
         {μ[β]α : trails[ μβ ] μα} →
         (e : term[ var ∘ cpsT ] τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β)
         {c : compatible (τ ⇒ α , μα) μβ μβ}
         (κ : cpsvalue[ var ] (cpsT τ) → cpsvalue[ var ] (cpsM μα) →
               cpsterm[ var ] (cpsT α))
         (k : var (cpsT τ ⇛ (cpsMs μ[β]α ⇛ cpsT α)))
         (t : var (cpsM μβ))
         (c' : compatible (τ ⇒ α , μα) μα μα) →
         (sch : schematicV′ κ) →
         cpsEqual {var}
          (CPSLet (CPSCons c (CPSVal (CPSVar k)) (CPSVal (CPSVar t)))
                  (λ kt → cpsTerm e (λ v t' → κ v t') (CPSVar kt)))
          (cpsTerm e (λ v t' →
                       CPSLet (CPSCons c' (CPSVal (CPSVar k)) (CPSVal t'))
                              (λ kt → κ v (CPSVar kt)))
                     (CPSVar t))

aux₄-s = {!!}
{-
aux₄-s (Val v) κ k t c' sch = {!!}
aux₄-s (App e e₁) κ k t c' sch = {!!}
aux₄-s {μβ = τ ⇒ τ' , μβ} (Plus e e₁) κ k t c' sch = {!!}
aux₄-s {μ[β]α = μ[β]α} (Control id₁ c₁ c₂ e) {c} κ k t c' sch = begin
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal
                     (CPSAppend c₂ (CPSCons c (CPSVar k) (CPSVar t))
                      (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' → κ (CPSVar v) (CPSVar t'')))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))

  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLetApp)))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSVal (CPSFun (λ t'' → κ (CPSVar z) (CPSVar t''))))
                 (CPSVal
                  (CPSAppend c₂ (CPSCons c (CPSVar k) (CPSVar t))
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rApp₂ (assoc {μ[β]α = μ[β]α} k (CPSVar t) (CPSCons c₁ (CPSVar x₁) (CPSVar x₂))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar z) (CPSVar x))))
                 (CPSVal
                  (CPSCons c' (CPSVar k)
                   (CPSAppend c₂ (CPSVar t)
                    (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp
                 (CPSVal
                  (CPSFun
                   (λ z₃ →
                      CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar z) (CPSVar x))))
                      (CPSVal (CPSCons c' (CPSVar k) (CPSVar z₃))))))
                 (CPSVal
                  (CPSAppend c₂ (CPSVar t)
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rApp₁ (rFun (λ x₃ → rBeta (sch (CPSCons c' (CPSVar k) (CPSVar x₃)) (CPSVar x)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp
                 (CPSVal
                  (CPSFun
                   (λ t'' → κ (CPSVar z) (CPSCons c' (CPSVar k) (CPSVar t'')))))
                 (CPSVal
                  (CPSAppend c₂ (CPSVar t)
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLetApp)))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal
                     (CPSAppend c₂ (CPSVar t) (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' → κ (CPSVar v) (CPSCons c' (CPSVar k) (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))
  ∎
aux₄-s (Prompt id₁ e) κ k t c' sch = {!!}
-}

-- idk v (k::t) -> k v t
aux : {var : cpstyp → Set} {α : typ} {μα : trail} {τ₂ : typ} {μ₃ : trail}
      {μ[∙]μ₃ : trails[ ∙ ] μ₃}
      {μ[μα]μ₃ : trails[ μα ] μ₃}
      (id : is-id-trails τ₂ α μ[∙]μ₃)
      (k : var (cpsT τ₂ ⇛ (cpsMs μ[μα]μ₃ ⇛ cpsT α)))
      (v : value[ var ∘ cpsT ] τ₂)
      (c : compatible (τ₂ ⇒ α , μ₃) μ₃ μ₃)
      (t : cpsvalue[ var ] cpsMs μ[μα]μ₃) →
      cpsEqual
      (CPSIdk id (CPSVal (cpsV v)) (CPSCons c (CPSVal (CPSVar k)) (CPSVal t)))
      (CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (cpsV v))) (CPSVal t))

aux {μ₃ = τ ⇒ τ' , ∙} id k v (refl , refl , c) t = begin
    (CPSIdk id (CPSVal (cpsV v))
     (CPSCons (refl , refl , c) (CPSVal (CPSVar k)) (CPSVal t)))
  ⟶⟨ rIdk₂ rConst ⟩
    CPSIdk id (CPSVal (cpsV v))
      (CPSVal
       (CPSFun
        (λ v₁ →
           CPSVal
           (CPSFun
            (λ t' →
               CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v₁)))
               (CPSCons refl (CPSVal t) (CPSVal (CPSVar t'))))))))
  ⟶⟨ rIdkt ⟩
    CPSApp
      (CPSApp
       (CPSVal
        (CPSFun
         (λ v₁ →
            CPSVal
            (CPSFun
             (λ t' →
                CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar v₁)))
                (CPSCons refl (CPSVal t) (CPSVal (CPSVar t'))))))))
       (CPSVal (cpsV v)))
      (CPSVal CPSIdt)
  ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
        sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))) ⟩
    CPSApp
      (CPSVal
       (CPSFun
        (λ z →
           CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (cpsV v)))
           (CPSCons refl (CPSVal t) (CPSVal (CPSVar z))))))
      (CPSVal CPSIdt)
  ⟶⟨ rBeta (sApp Subst≠ (sCon Subst≠ (sVal sVar=))) ⟩
    CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (cpsV v)))
      (CPSCons refl (CPSVal t) (CPSVal CPSIdt))
  ⟷⟨ eApp₂ (eReduce (rConsid)) ⟩
    CPSApp (CPSApp (CPSVal (CPSVar k)) (CPSVal (cpsV v))) (CPSVal t)
  ∎

------------------------------------------------------------------------------------------------------------------

correctEta : {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail}
             {μs : trails[ μβ ] μα} →
             {e e′ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                  cpsterm[ var ] (cpsT α)) →
             (t : cpsvalue[ var ] (cpsM μβ)) →
             (sch : schematicV k) →
             (sch' : schematicV′ k) →
             (red : Reduce e e′) →
             cpsEqual (cpsTerm e k t) (cpsTerm e′ k t)

correctEta {μs = μs} {e′ = e′} k t sch sch' (RBeta {e₁ = e₁} {v₂ = v₂} sub) =
  begin
    cpsTerm {μs = μs} (App (Val (Fun e₁)) (Val v₂)) k t
  ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ t' →
        ekSubst sub (λ v → sApp (sApp Subst≠ (sVal v)) Subst≠)))))))) ⟩
    CPSApp
      (CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                cpsTerm e′
                (λ v t'' →
                   CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v)) (CPSVal t''))
                (CPSVar z₁))))))
       (CPSVal
        (CPSFun
         (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
      (CPSVal t)
  ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ →
        kSubst′′ e′ (λ x → sApp (sApp (sVal sVar=) (sVal x)) Subst≠))))) ⟩
    CPSApp
      (CPSVal
       (CPSFun
        (λ z →
           cpsTerm e′
           (λ z₁ z₂ →
              CPSApp
              (CPSApp
               (CPSVal
                (CPSFun
                 (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
               (CPSVal z₁))
              (CPSVal z₂))
           (CPSVar z))))
      (CPSVal t)
  ⟶⟨ rBeta (tSubst e′ λ t₁ v₃ → sApp Subst≠ (sVal sVar=)) ⟩
    cpsTerm e′
      (λ z₁ z₂ →
         CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
          (CPSVal z₁))
         (CPSVal z₂))
      t
  ⟷⟨ correctCont e′ _
       (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
       (λ v t₁ → begin
           (CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ → CPSVal (CPSFun (λ t'' → k (CPSVar v₁) (CPSVar t''))))))
             (CPSVal (cpsV v)))
            (CPSVal t₁))
         ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x → sch v (CPSVar x))))) ⟩
           CPSApp (CPSVal (CPSFun (λ z → k (cpsV v) (CPSVar z)))) (CPSVal t₁)
         ⟶⟨ rBeta (sch' t₁ (cpsV v)) ⟩
           (k (cpsV v) t₁)
         ∎) ⟩
    cpsTerm e′ k t
  ∎

correctEta k t sch sch' (RPlus {τ₂} {μα} {n₁} {n₂}) =
  begin
    (CPSLet (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂)))
     (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rPlus ⟩
    CPSLet (CPSVal (CPSNum (n₁ + n₂))) (λ v → k (CPSVar v) t)
  ⟶⟨ rLet (sch (Num (n₁ + n₂)) t) ⟩
    (k (CPSNum (n₁ + n₂)) t)
  ∎

correctEta k t sch sch' (RFrame (App₁ e₂) red) =
  correctEta _ t
    (λ v₁ t₁ → kSubst e₂ (λ v₂ t₂ →
                 sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))
    (λ t₁ v₁ → tSubst e₂ (λ t₂ v₂ → sApp (sApp Subst≠ Subst≠) (sVal sVar=)))
    red

correctEta k t sch sch' (RFrame (App₂ v₁) red) =
  correctEta _ t
    (λ v₁ t₁ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
    (λ t₁ v₁ → sApp Subst≠ (sVal sVar=))
    red

correctEta k t sch sch' (RFrame (Plus₁ e₂) red) =
  correctEta _ t
    (λ v₁ t₁ → kSubst e₂ (λ v₂ t₂ →
                 sLet (λ n → Subst≠)
                      (λ n → sPlu (sVal sVar=) Subst≠)))
    (λ t₁ v₁ → tSubst e₂ (λ t₂ v₂ →
                 sLet (λ x₁ → sch' t₂ (CPSVar x₁)) (λ x₁ → Subst≠)))
    red

correctEta k t sch sch' (RFrame (Plus₂ v₁) red) =
  correctEta _ t
    (λ v₁ t₁ → sLet (λ n → Subst≠)
                    (λ n → sPlu Subst≠ (sVal sVar=)))
    (λ t₁ v₁ → sLet (λ n → sch' t₁ (CPSVar n))
                    (λ n → Subst≠))
    red

correctEta k t sch sch' (RFrame {e₁ = e₁} {e₂ = e₂} (Pro id) red) =
  begin
    (CPSLet (cpsTerm e₁ (λ v t → CPSIdk id (CPSVal v) (CPSVal t)) CPSIdt)
            (λ v → k (CPSVar v) t))
  ⟷⟨ eLet₁ (correctEta _ CPSIdt
               (λ v₁ t₁ → sIdk (sVal sVar=) Subst≠)
               (λ t₁ v₁ → sIdk Subst≠ (sVal sVar=))
               red) ⟩
    (CPSLet (cpsTerm e₂ (λ v t → CPSIdk id (CPSVal v) (CPSVal t)) CPSIdt)
            (λ v → k (CPSVar v) t))
  ∎

correctEta k t sch sch' (RPrompt {v₁ = v₁}) =
  begin
    (CPSLet (CPSIdk refl (CPSVal (cpsV v₁)) (CPSVal CPSIdt))
            (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rIdkid ⟩
    CPSLet (CPSVal (cpsV v₁)) (λ v → k (CPSVar v) t)
  ⟷⟨ eLetApp ⟩
    CPSApp (CPSVal (CPSFun (λ v → k (CPSVar v) t))) (CPSVal (cpsV v₁))
  ⟶⟨ rBeta (sch v₁ t) ⟩
    (k (cpsV v₁) t)
  ∎

correctEta {μα = τ ⇒ τ' , ∙} k t sch sch'
           (RControl {μ[∙]α = μ[∙]α} {μ[∙]μ₃ = μ[∙]μ₃}
                     {μ[μα]μ₃ = μ[μα]μ₃}
                     p₁ p₂ {id₀} id (refl , refl , refl) refl same e) =

  begin
      (CPSLet
       (cpsTerm
        (pcontext-plug p₁ (Control id (refl , refl , refl) refl e))
        (λ v t₁ → CPSIdk id₀ (CPSVal v) (CPSVal t₁)) CPSIdt)
       (λ v → k (CPSVar v) t))
  ⟷⟨ eLet₁ (control-lemma p₁ p₂ refl same
                           (Control id (refl , refl , refl) refl e)
                           (λ v t → CPSIdk id₀ (CPSVal v) (CPSVal t)) CPSIdt
                           (λ v t₁ → sIdk (sVal sVar=) Subst≠)
                           (λ t₁ v₂ → sIdk Subst≠ (sVal sVar=))) ⟩
    CPSLet
      (cpsTerm {μs = μ[∙]μ₃}
       (App {μ[γ]β = μ[∙]α}
            (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))
        (Control {μs₁ = μ[μα]μ₃} id (refl , refl , refl) refl e))
       (λ v t₁ → CPSIdk id₀ (CPSVal v) (CPSVal t₁)) CPSIdt)
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
        eApp₁ (eApp₁ (eReduce (rBeta (sVal (sFun (λ k → sVal (sFun (λ t →
          eSubst (subst-context p₂ (Var x₁))
                 (λ sub → sApp (sApp Subst≠ (sVal sub)) Subst≠))))))))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ z₄ →
                             CPSVal
                             (CPSFun
                              (λ z₅ →
                                 cpsTerm (pcontext-plug p₂ (Val (Var z)))
                                 (λ v t'' →
                                    CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                                 (CPSVar z₅))))))
                        (CPSVal
                         (CPSFun
                          (λ v →
                             CPSVal
                             (CPSFun
                              (λ t'' → CPSIdk id₀ (CPSVal (CPSVar v)) (CPSVal (CPSVar t''))))))))
                       (CPSVal (CPSVar z₃))))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
        eApp₁ (eReduce (rBeta (sVal (sFun (λ x₅ →
          kSubst (pcontext-plug p₂ (Val (Var x₁)))
            (λ x₆ t₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ z₄ →
                            cpsTerm (pcontext-plug p₂ (Val (Var z)))
                            (λ z₅ z₆ →
                               CPSApp
                               (CPSApp
                                (CPSVal
                                 (CPSFun
                                  (λ v →
                                     CPSVal
                                     (CPSFun
                                      (λ t'' → CPSIdk id₀ (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
                                (CPSVal z₅))
                               (CPSVal z₆))
                            (CPSVar z₄))))
                       (CPSVal (CPSVar z₃))))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
       eReduce (rBeta (tSubst (pcontext-plug p₂ (Val (Var x₁)))
                     (λ t₁ v₂ → sApp Subst≠ (sVal sVar=)))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ z₅ z₆ →
                          CPSApp
                          (CPSApp
                           (CPSVal
                            (CPSFun
                             (λ v →
                                CPSVal
                                (CPSFun
                                 (λ t'' → CPSIdk id₀ (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
                           (CPSVal z₅))
                          (CPSVal z₆))
                       (CPSVar z₃)))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
      correctCont (pcontext-plug p₂ (Val (Var x₁))) _
        (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t₁ → eReduce (rApp₁ (rBeta (sVal (sFun (λ x →
          sIdk (sVal sVar=) Subst≠)))))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ z₅ z₆ →
                          CPSApp (CPSVal
                                (CPSFun
                                 (λ t'' → CPSIdk id₀ (CPSVal z₅) (CPSVal (CPSVar t'')))))
                          (CPSVal z₆))
                       (CPSVar z₃)))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
      correctCont (pcontext-plug p₂ (Val (Var x₁))) _
        {k₂ = λ v t'' → CPSIdk id₀ (CPSVal v) (CPSVal t'')}
        (λ v t₁ → sApp (sVal (sFun (λ x₅ → sIdk (sVal sVar=) Subst≠))) Subst≠)
        (λ v t₁ → eReduce (rBeta (sIdk Subst≠ (sVal sVar=)))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ v t'' → CPSIdk id₀ (CPSVal v) (CPSVal t'')) (CPSVar z₃)))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ →
        eLet₁ eApdidΩ))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSCons (refl , refl , refl) (CPSVal (CPSVar z₁))
                     (CPSVal (CPSVar z₂)))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ v t'' → CPSIdk id₀ (CPSVal v) (CPSVal t'')) (CPSVar z₃)))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x → eFun (λ x₁ → eFun (λ x₂ →
        aux₄-s (pcontext-plug p₂ (Val (Var x)))
                (λ v t'' → CPSIdk id₀ (CPSVal v) (CPSVal t'')) x₁ x₂
                (extend-compatible' (refl , refl , refl)
                                    (proj₂ (diff-compatible μ[μα]μ₃)))
                (λ t₁ v₂ → sIdk Subst≠ (sVal sVar=)) ))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ v t' →
                       CPSLet
                       (CPSCons
                        (extend-compatible' (refl , refl , refl)
                         (proj₂ (diff-compatible μ[μα]μ₃)))
                        (CPSVal (CPSVar z₁)) (CPSVal t'))
                       (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))
                    (CPSVar z₂))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ z → eFun (λ z₁ → eFun (λ z₂ →
        correctCont (pcontext-plug p₂ (Val (Var z)))
        (λ v t' →
                       CPSLet
                       (CPSCons
                        (extend-compatible' (refl , refl , refl)
                         (proj₂ (diff-compatible μ[μα]μ₃)))
                        (CPSVal (CPSVar z₁)) (CPSVal t'))
                       (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))
        {k₂ = (λ v t' →
                       CPSLet
                       (CPSVal (CPSFun (λ v0 → CPSVal (CPSFun (λ t0 →
                         CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v0)))
                                (CPSCons
                                  refl
                                  (CPSVal t') (CPSVal (CPSVar t0))))))))
                       (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))}
        (λ v t₁ → sLet (λ x₃ → sIdk (sVal sVar=) Subst≠) (λ x₃ → Subst≠))
        (λ v t₁ → eReduce (rLet₁ (rConst {c₂ = refl})))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ v t' →
                       CPSLet
                       (CPSVal
                        (CPSFun
                         (λ v0 →
                            CPSVal
                            (CPSFun
                             (λ t0 →
                                CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v0)))
                                (CPSCons refl (CPSVal t') (CPSVal (CPSVar t0))))))))
                       (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))
                    (CPSVar z₂))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x → eFun (λ x₁ → eFun (λ x₂ →
        correctCont (pcontext-plug p₂ (Val (Var x)))
        (λ v t' →
            CPSLet
            (CPSVal
             (CPSFun
              (λ v0 →
                 CPSVal
                 (CPSFun
                  (λ t0 →
                     CPSApp (CPSApp (CPSVal (CPSVar x₁)) (CPSVal (CPSVar v0)))
                     (CPSCons refl (CPSVal t') (CPSVal (CPSVar t0))))))))
            (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))
        {k₂ = λ v t' →
            CPSIdk id₀ (CPSVal v) (CPSVal (CPSFun
              (λ v0 →
                 CPSVal
                 (CPSFun
                  (λ t0 →
                     CPSApp (CPSApp (CPSVal (CPSVar x₁)) (CPSVal (CPSVar v0)))
                     (CPSCons refl (CPSVal t') (CPSVal (CPSVar t0))))))))}
        (λ v t₁ → sLet (λ x₃ → sIdk (sVal sVar=) Subst≠) (λ x₃ → Subst≠))
        (λ v t₁ → eReduce (rLet (sIdk Subst≠ (sVal sVar=))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z))) (λ v t' →
                                                                 CPSIdk id₀ (CPSVal v)
                                                                 (CPSVal
                                                                  (CPSFun
                                                                   (λ v0 →
                                                                      CPSVal
                                                                      (CPSFun
                                                                       (λ t0 →
                                                                          CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v0)))
                                                                          (CPSCons refl (CPSVal t') (CPSVal (CPSVar t0))))))))) (CPSVar z₂))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x → eFun (λ x₁ → eFun (λ x₂ →
        correctCont (pcontext-plug p₂ (Val (Var x))) _
        (λ v t₁ → sIdk (sVal sVar=) Subst≠)
        (λ v t₁ → eReduce′ (rIdk₂ (rConst {c₂ = refl})))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ z₃ z₄ →
                       CPSIdk id₀ (CPSVal z₃)
                       (CPSCons
                        (extend-compatible' (refl , refl , refl)
                         (proj₂ (diff-compatible μ[μα]μ₃)))
                        (CPSVal (CPSVar z₁)) (CPSVal z₄)))
                    (CPSVar z₂))))))))
       (λ z →
          cpsTerm (e z) (λ v t'' → CPSIdk id (CPSVal v) (CPSVal t''))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x → eFun (λ x₁ → eFun (λ x₂ →
        correctCont (pcontext-plug p₂ (Val (Var x))) _
        (λ v t₁ → sIdk (sVal sVar=) Subst≠)
        (λ v t₁ → aux {μ[∙]μ₃ = μ[∙]μ₃} {μ[μα]μ₃ = μ[μα]μ₃}
                       id₀ x₁ v (extend-compatible' (refl , refl , refl)
                       (proj₂ (diff-compatible μ[μα]μ₃))) t₁)))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ z →
          cpsTerm (e z) (λ v t'' → CPSIdk id (CPSVal v) (CPSVal t''))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₂ (λ x₁ →
      correctCont (e x₁) _
        {k₂ = λ v t'' → CPSIdk id (CPSVal v) (CPSVal t'')} (λ v t₁ →
        sApp (sVal (sFun (λ x₂ → sIdk (sVal sVar=) Subst≠))) Subst≠)
        (λ v t₁ → eReduce (rBeta (sIdk Subst≠ (sVal sVar=)))))) ⟩′
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ z →
          cpsTerm (e z)
          (λ v t'' →
             CPSApp
             (CPSVal
              (CPSFun (λ t''' → CPSIdk id (CPSVal v) (CPSVal (CPSVar t''')))))
             (CPSVal t''))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₂ (λ x₁ →
      correctCont (e x₁) _
        {k₂ =
         λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' →
             CPSIdk id (CPSVal v) (CPSVal (CPSVar t''')))))
           (CPSVal t'')}
        (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t₁ → eReduce (rApp₁ (rBeta (sVal (sFun (λ x →
          sIdk (sVal sVar=) Subst≠)))))))) ⟩′
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ z →
          cpsTerm (e z)
          (λ z₁ z₂ →
             CPSApp
             (CPSApp
              (CPSVal
               (CPSFun
                (λ v →
                   CPSVal
                   (CPSFun
                    (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
              (CPSVal z₁))
             (CPSVal z₂))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₂ (λ x₁ →
        eReduce′ (rBeta (tSubst (e x₁) (λ t₁ v₂ →
          sApp Subst≠ (sVal sVar=)))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ x →
          CPSApp
          (CPSVal
           (CPSFun
            (λ z₁ →
               cpsTerm (e x)
               (λ z₂ z₃ →
                  CPSApp
                  (CPSApp
                   (CPSVal
                    (CPSFun
                     (λ v →
                        CPSVal
                        (CPSFun
                         (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
                   (CPSVal z₂))
                  (CPSVal z₃))
               (CPSVar z₁))))
          (CPSVal CPSIdt)))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ eLet₃ ⟩′
    CPSLet
      (CPSApp
       (CPSLet
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (pcontext-plug p₂ (Val (Var x)))
                     (λ v t'' →
                        CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                     (CPSVar t'))))))))
        (λ z →
           CPSVal
           (CPSFun
            (λ z₁ →
               cpsTerm (e z)
               (λ z₂ z₃ →
                  CPSApp
                  (CPSApp
                   (CPSVal
                    (CPSFun
                     (λ v →
                        CPSVal
                        (CPSFun
                         (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
                   (CPSVal z₂))
                  (CPSVal z₃))
               (CPSVar z₁)))))
       (CPSVal CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eApp₁ (eLet₂ (λ x₁ → eReduce′ (rBeta (sVal (sFun (λ x₂ →
        kSubst (e x₁)
          (λ x₃ t₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))) ⟩
    CPSLet
      (CPSApp
       (CPSLet
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (pcontext-plug p₂ (Val (Var x)))
                     (λ v t'' →
                        CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                     (CPSVar t'))))))))
        (λ x →
           CPSApp
           (CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (e x)
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))
           (CPSVal
            (CPSFun
             (λ v →
                CPSVal
                (CPSFun
                 (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))))
       (CPSVal CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eApp₁ eLet₃) ⟩′
    CPSLet
      (CPSApp
       (CPSApp
        (CPSLet
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v t'' →
                         CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                      (CPSVar t'))))))))
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (e x)
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t')))))))
        (CPSVal
         (CPSFun
          (λ v →
             CPSVal
             (CPSFun
              (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t''))))))))
       (CPSVal CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eApp₁ (eApp₁ eLetApp)) ⟩
      (CPSLet
       (CPSApp
        (CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ x →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (e x)
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t'))))))))
          (CPSVal
           (CPSFun
            (λ x →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (pcontext-plug p₂ (Val (Var x)))
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t')))))))))
         (CPSVal
          (CPSFun
           (λ v →
              CPSVal
              (CPSFun
               (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t''))))))))
        (CPSVal CPSIdt))
       (λ v → k (CPSVar v) t))
  ∎

correctEta {μα = τ ⇒ τ' , (τ₁ ⇒ τ'' , μα)} k t sch sch'
           (RControl {μ₃ = .τ ⇒ .τ' , ∙} {μ[∙]α = μ[∙]α}
           {μ[∙]μ₃ = μ[∙]μ₃} {μ[μα]μ₃ = μ[μα]μ₃}
           p₁ p₂ {id₀} id (refl , refl , refl , refl , c₁) refl same e) =

  begin
      (CPSLet
       (cpsTerm (pcontext-plug p₁ (Control id (refl , refl , refl , refl , c₁) refl e))
        (λ v t₁ → CPSIdk id₀ (CPSVal v) (CPSVal t₁)) CPSIdt)
       (λ v → k (CPSVar v) t))
  ⟷⟨ eLet₁ (control-lemma p₁ p₂ refl same
                           (Control id (refl , refl , refl , refl , c₁) refl e)
                           (λ v t → CPSIdk id₀ (CPSVal v) (CPSVal t)) CPSIdt
                           (λ v t₁ → sIdk (sVal sVar=) Subst≠)
                           (λ t₁ v₂ → sIdk Subst≠ (sVal sVar=))) ⟩
    CPSLet
      (cpsTerm {μs = μ[∙]μ₃}
       (App {μ[γ]β = μ[∙]α}
            (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))
        (Control {μs₁ = μ[μα]μ₃} id (refl , refl , refl , refl , c₁) refl e))
       (λ v t₁ → CPSIdk id₀ (CPSVal v) (CPSVal t₁)) CPSIdt)
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
        eApp₁ (eApp₁ (eReduce (rBeta (sVal (sFun (λ k → sVal (sFun (λ t →
          eSubst (subst-context p₂ (Var x₁))
                 (λ sub → sApp (sApp Subst≠ (sVal sub)) Subst≠))))))))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl , refl , c₁) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ z₄ →
                             CPSVal
                             (CPSFun
                              (λ z₅ →
                                 cpsTerm (pcontext-plug p₂ (Val (Var z)))
                                 (λ v t'' →
                                    CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                                 (CPSVar z₅))))))
                        (CPSVal
                         (CPSFun
                          (λ v →
                             CPSVal
                             (CPSFun
                              (λ t'' → CPSIdk id₀ (CPSVal (CPSVar v)) (CPSVal (CPSVar t''))))))))
                       (CPSVal (CPSVar z₃))))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
        eApp₁ (eReduce (rBeta (sVal (sFun (λ x₅ →
          kSubst (pcontext-plug p₂ (Val (Var x₁)))
            (λ x₆ t₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl , refl , c₁) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ z₄ →
                            cpsTerm (pcontext-plug p₂ (Val (Var z)))
                            (λ z₅ z₆ →
                               CPSApp
                               (CPSApp
                                (CPSVal
                                 (CPSFun
                                  (λ v →
                                     CPSVal
                                     (CPSFun
                                      (λ t'' → CPSIdk id₀ (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
                                (CPSVal z₅))
                               (CPSVal z₆))
                            (CPSVar z₄))))
                       (CPSVal (CPSVar z₃))))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
       eReduce (rBeta (tSubst (pcontext-plug p₂ (Val (Var x₁)))
                     (λ t₁ v₂ → sApp Subst≠ (sVal sVar=)))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl , refl , c₁) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ z₅ z₆ →
                          CPSApp
                          (CPSApp
                           (CPSVal
                            (CPSFun
                             (λ v →
                                CPSVal
                                (CPSFun
                                 (λ t'' → CPSIdk id₀ (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
                           (CPSVal z₅))
                          (CPSVal z₆))
                       (CPSVar z₃)))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
      correctCont (pcontext-plug p₂ (Val (Var x₁))) _
        (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t₁ → eReduce (rApp₁ (rBeta (sVal (sFun (λ x →
          sIdk (sVal sVar=) Subst≠)))))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl , refl , c₁) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ z₅ z₆ →
                          CPSApp (CPSVal
                                (CPSFun
                                 (λ t'' → CPSIdk id₀ (CPSVal z₅) (CPSVal (CPSVar t'')))))
                          (CPSVal z₆))
                       (CPSVar z₃)))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ → eLet₂ (λ x₄ →
      correctCont (pcontext-plug p₂ (Val (Var x₁))) _
        {k₂ = λ v t'' → CPSIdk id₀ (CPSVal v) (CPSVal t'')}
        (λ v t₁ → sApp (sVal (sFun (λ x₅ → sIdk (sVal sVar=) Subst≠))) Subst≠)
        (λ v t₁ → eReduce (rBeta (sIdk Subst≠ (sVal sVar=)))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSAppend refl (CPSVal CPSIdt)
                     (CPSCons (refl , refl , refl , refl , c₁) (CPSVal (CPSVar z₁))
                      (CPSVal (CPSVar z₂))))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ v t'' → CPSIdk id₀ (CPSVal v) (CPSVal t'')) (CPSVar z₃)))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x₁ → eFun (λ x₂ → eFun (λ x₃ →
        eLet₁ eApdidΩ))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSCons (refl , refl , refl , refl , c₁) (CPSVal (CPSVar z₁))
                     (CPSVal (CPSVar z₂)))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ v t'' → CPSIdk id₀ (CPSVal v) (CPSVal t'')) (CPSVar z₃)))))))))
       (λ x' →
          cpsTerm (e x') (λ v t₁ → CPSIdk id (CPSVal v) (CPSVal t₁)) CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x → eFun (λ x₁ → eFun (λ x₂ →
        aux₄-s (pcontext-plug p₂ (Val (Var x)))
                (λ v t'' → CPSIdk id₀ (CPSVal v) (CPSVal t'')) x₁ x₂
                (extend-compatible' (refl , refl , refl , refl , c₁)
                                    (proj₂ (diff-compatible μ[μα]μ₃)))
                (λ t₁ v₂ → sIdk Subst≠ (sVal sVar=)) ))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ v t' →
                       CPSLet
                       (CPSCons
                        (extend-compatible' (refl , refl , refl , refl , c₁)
                         (proj₂ (diff-compatible μ[μα]μ₃)))
                        (CPSVal (CPSVar z₁)) (CPSVal t'))
                       (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))
                    (CPSVar z₂))))))))
       (λ z →
          cpsTerm (e z) (λ v t'' → CPSIdk id (CPSVal v) (CPSVal t''))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ z → eFun (λ z₁ → eFun (λ z₂ →
        correctCont (pcontext-plug p₂ (Val (Var z)))
        (λ v t' →
                       CPSLet
                       (CPSCons
                        (extend-compatible' (refl , refl , refl , refl , c₁)
                         (proj₂ (diff-compatible μ[μα]μ₃)))
                        (CPSVal (CPSVar z₁)) (CPSVal t'))
                       (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))
        {k₂ = (λ v t' →
                       CPSLet
                       (CPSVal (CPSFun (λ v0 → CPSVal (CPSFun (λ t0 →
                         CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v0)))
                                (CPSCons
                                  refl
                                  (CPSVal t') (CPSVal (CPSVar t0))))))))
                       (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))}
        (λ v t₁ → sLet (λ x₃ → sIdk (sVal sVar=) Subst≠) (λ x₃ → Subst≠))
        (λ v t₁ → eReduce (rLet₁ (rConst {c₂ = refl})))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ v t' →
                       CPSLet
                       (CPSVal
                        (CPSFun
                         (λ v0 →
                            CPSVal
                            (CPSFun
                             (λ t0 →
                                CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v0)))
                                (CPSCons refl (CPSVal t') (CPSVal (CPSVar t0))))))))
                       (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))
                    (CPSVar z₂))))))))
       (λ z →
          cpsTerm (e z) (λ v t'' → CPSIdk id (CPSVal v) (CPSVal t''))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x → eFun (λ x₁ → eFun (λ x₂ →
        correctCont (pcontext-plug p₂ (Val (Var x)))
        (λ v t' →
            CPSLet
            (CPSVal
             (CPSFun
              (λ v0 →
                 CPSVal
                 (CPSFun
                  (λ t0 →
                     CPSApp (CPSApp (CPSVal (CPSVar x₁)) (CPSVal (CPSVar v0)))
                     (CPSCons refl (CPSVal t') (CPSVal (CPSVar t0))))))))
            (λ kt → CPSIdk id₀ (CPSVal v) (CPSVal (CPSVar kt))))
        {k₂ = λ v t' →
            CPSIdk id₀ (CPSVal v) (CPSVal (CPSFun
              (λ v0 →
                 CPSVal
                 (CPSFun
                  (λ t0 →
                     CPSApp (CPSApp (CPSVal (CPSVar x₁)) (CPSVal (CPSVar v0)))
                     (CPSCons refl (CPSVal t') (CPSVal (CPSVar t0))))))))}
        (λ v t₁ → sLet (λ x₃ → sIdk (sVal sVar=) Subst≠) (λ x₃ → Subst≠))
        (λ v t₁ → eReduce (rLet (sIdk Subst≠ (sVal sVar=))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ z₃ z₄ →
                       CPSIdk id₀ (CPSVal z₃)
                       (CPSVal
                        (CPSFun
                         (λ v →
                            CPSVal
                            (CPSFun
                             (λ t' →
                                CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v)))
                                (CPSCons refl (CPSVal z₄) (CPSVal (CPSVar t')))))))))
                    (CPSVar z₂))))))))
       (λ z →
          cpsTerm (e z) (λ v t'' → CPSIdk id (CPSVal v) (CPSVal t''))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x → eFun (λ x₁ → eFun (λ x₂ →
        correctCont (pcontext-plug p₂ (Val (Var x))) _
        (λ v t₁ → sIdk (sVal sVar=) Subst≠)
        (λ v t₁ → eReduce′ (rIdk₂ (rConst {c₂ = refl})))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ z₃ z₄ →
                       CPSIdk id₀ (CPSVal z₃)
                       (CPSCons
                        (extend-compatible' (refl , refl , refl , refl , c₁)
                         (proj₂ (diff-compatible μ[μα]μ₃)))
                        (CPSVal (CPSVar z₁)) (CPSVal z₄)))
                    (CPSVar z₂))))))))
       (λ z →
          cpsTerm (e z) (λ v t'' → CPSIdk id (CPSVal v) (CPSVal t''))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₁ (eFun (λ x → eFun (λ x₁ → eFun (λ x₂ →
        correctCont (pcontext-plug p₂ (Val (Var x))) _
        (λ v t₁ → sIdk (sVal sVar=) Subst≠)
        (λ v t₁ → aux {μ[∙]μ₃ = μ[∙]μ₃} {μ[μα]μ₃ = μ[μα]μ₃}
                       id₀ x₁ v (extend-compatible' (refl , refl , refl , refl , c₁)
                       (proj₂ (diff-compatible μ[μα]μ₃))) t₁)))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ z →
          cpsTerm (e z) (λ v t'' → CPSIdk id (CPSVal v) (CPSVal t''))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₂ (λ x₁ →
      correctCont (e x₁) _
        {k₂ = λ v t'' → CPSIdk id (CPSVal v) (CPSVal t'')} (λ v t₁ →
        sApp (sVal (sFun (λ x₂ → sIdk (sVal sVar=) Subst≠))) Subst≠)
        (λ v t₁ → eReduce (rBeta (sIdk Subst≠ (sVal sVar=)))))) ⟩′
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ z →
          cpsTerm (e z)
          (λ v t'' →
             CPSApp
             (CPSVal
              (CPSFun (λ t''' → CPSIdk id (CPSVal v) (CPSVal (CPSVar t''')))))
             (CPSVal t''))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₂ (λ x₁ →
      correctCont (e x₁) _
        {k₂ =
         λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' →
             CPSIdk id (CPSVal v) (CPSVal (CPSVar t''')))))
           (CPSVal t'')}
        (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t₁ → eReduce (rApp₁ (rBeta (sVal (sFun (λ x →
          sIdk (sVal sVar=) Subst≠)))))))) ⟩′
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ z →
          cpsTerm (e z)
          (λ z₁ z₂ →
             CPSApp
             (CPSApp
              (CPSVal
               (CPSFun
                (λ v →
                   CPSVal
                   (CPSFun
                    (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
              (CPSVal z₁))
             (CPSVal z₂))
          CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eLet₂ (λ x₁ →
        eReduce′ (rBeta (tSubst (e x₁) (λ t₁ v₂ →
          sApp Subst≠ (sVal sVar=)))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ x →
          CPSApp
          (CPSVal
           (CPSFun
            (λ z₁ →
               cpsTerm (e x)
               (λ z₂ z₃ →
                  CPSApp
                  (CPSApp
                   (CPSVal
                    (CPSFun
                     (λ v →
                        CPSVal
                        (CPSFun
                         (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
                   (CPSVal z₂))
                  (CPSVal z₃))
               (CPSVar z₁))))
          (CPSVal CPSIdt)))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ eLet₃ ⟩′
    CPSLet
      (CPSApp
       (CPSLet
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (pcontext-plug p₂ (Val (Var x)))
                     (λ v t'' →
                        CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                     (CPSVar t'))))))))
        (λ z →
           CPSVal
           (CPSFun
            (λ z₁ →
               cpsTerm (e z)
               (λ z₂ z₃ →
                  CPSApp
                  (CPSApp
                   (CPSVal
                    (CPSFun
                     (λ v →
                        CPSVal
                        (CPSFun
                         (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))
                   (CPSVal z₂))
                  (CPSVal z₃))
               (CPSVar z₁)))))
       (CPSVal CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eApp₁ (eLet₂ (λ x₁ → eReduce′ (rBeta (sVal (sFun (λ x₂ →
        kSubst (e x₁)
          (λ x₃ t₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))) ⟩
    CPSLet
      (CPSApp
       (CPSLet
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (pcontext-plug p₂ (Val (Var x)))
                     (λ v t'' →
                        CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                     (CPSVar t'))))))))
        (λ x →
           CPSApp
           (CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (e x)
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))
           (CPSVal
            (CPSFun
             (λ v →
                CPSVal
                (CPSFun
                 (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t'')))))))))
       (CPSVal CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eApp₁ eLet₃) ⟩′
    CPSLet
      (CPSApp
       (CPSApp
        (CPSLet
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v t'' →
                         CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                      (CPSVar t'))))))))
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (e x)
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t')))))))
        (CPSVal
         (CPSFun
          (λ v →
             CPSVal
             (CPSFun
              (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t''))))))))
       (CPSVal CPSIdt))
      (λ v → k (CPSVar v) t)
  ⟷⟨ eLet₁ (eApp₁ (eApp₁ eLetApp)) ⟩
      (CPSLet
       (CPSApp
        (CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ x →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (e x)
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t'))))))))
          (CPSVal
           (CPSFun
            (λ x →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (pcontext-plug p₂ (Val (Var x)))
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t')))))))))
         (CPSVal
          (CPSFun
           (λ v →
              CPSVal
              (CPSFun
               (λ t'' → CPSIdk id (CPSVal (CPSVar v)) (CPSVal (CPSVar t''))))))))
        (CPSVal CPSIdt))
       (λ v → k (CPSVar v) t))
  ∎
