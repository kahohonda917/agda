module lemma1 where

open import DSt
open import CPSt

open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality


correctContI : {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail}→
               {e₁ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
               (k₁ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
               (k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
               (trail : cpsvalue[ var ] (cpsM μβ)) →
               ((v : value[ var ∘ cpsT ] τ₁) →
                (t : cpsvalue[ var ] (cpsM μα)) →
                cpsreduce (k₁ (cpsV v) t) (k₂ (cpsV v) t)) →
               cpsreduce (cpsTerm e₁ k₁ trail) (cpsTerm e₁ k₂ trail)

correctContI k₁ k₂ trail₁ x = {!!}



subst-cont  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  {t : var τ₃ → cpsvalue[ var ] (cpsM μα)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  cpsSubstVal (λ x → v₁ x) v v₁′ →
  cpsSubstVal (λ x → t x) v t′ →
  cpsSubst (λ x → k₁ x (v₁′) (t′)) v (k₂ v₁′ t′)

subst-trail  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
              (t₁ : var τ₃ → cpsvalue[ var ] (cpsM μα)) →
              (v : cpsvalue[ var ] τ₃) →
              (t₂ : cpsvalue[ var ] (cpsM μα)) → Set

subst-trail {var} {τ₁} {τ₂} {μα}  {τ₃} t₁ v t₂ =
  {k : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)} →
  {k′ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)} →
  {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  cpsSubst (λ x → k x v₁′ t₂) v (k′ v₁′ t₂) →
  cpsSubstVal (λ x → v₁ x) v v₁′ →
  cpsSubst (λ x → k′ v₁′ (t₁ x)) v (k′ v₁′ t₂)

mutual
  SubstV≠ : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsvalue[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubstVal (λ y → t) v t

  SubstV≠ {var} {t = CPSVar x} = sVar≠
  SubstV≠ {var} {t = CPSNum n} = sNum
  SubstV≠ {var} {t = CPSFun e} = sFun λ x → Subst≠
  SubstV≠ {var} {t = CPSId} = sId
  SubstV≠ {var} {t = CPSTrail t} = sTra SubstV≠

  Subst≠  : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsterm[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubst (λ y → t) v t

  Subst≠ {t = CPSVal x} = sVal SubstV≠
  Subst≠ {t = CPSApp t t₁} = sApp Subst≠ Subst≠
  Subst≠ {t = CPSLet t x} = sLet (λ y → Subst≠) (λ y₂ → Subst≠)
  Subst≠ {t = CPSPlus t t₁} = sPlu Subst≠ Subst≠
  Subst≠ {t = CPSIdk x x₁ t} = sIdk SubstV≠ SubstV≠
  Subst≠ {t = CPSAppend x t t₁} = sApd Subst≠ Subst≠
  Subst≠ {t = CPSCons x t t₁} = sCon Subst≠ Subst≠

mutual

  SubstV-id  : {var : typ → Set}{τ₁ τ₂ : typ} →
               {v₁ : value[ var ] τ₁} →
               {v : value[ var ] τ₂} →
                SubstVal (λ _ → v₁) v v₁

  SubstV-id {var} {τ₁} {τ₂} {Var x} {v} = sVar≠
  SubstV-id {var} {.Nat} {τ₂} {Num n} {v} = sNum
  SubstV-id {var} {.(_ ⇒ _ ⟨ _ ⟩ _ ⟨ _ ⟩ _)} {τ₂} {Fun e₁} {v} = sFun λ x → Subst-id


  Subst-id  : {var : typ → Set}{τ₁ τ₂ α β : typ}{μα μβ : trail} →
              {t : term[ var ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
              {v : value[ var ] τ₂} →
                Subst (λ _ → t) v t

  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα} {Val x} {v} = sVal SubstV-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {App t t₁} {v} = sApp Subst-id Subst-id
  Subst-id {var} {.Nat} {τ₂} {α} {β} {μα} {μβ} {Plus t t₁} {v} = sPlu Subst-id Subst-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {Control x x₁ x₂ e} {v} = sCon (λ k → Subst-id)
  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα} {Prompt x t} {v} = sPro Subst-id

mutual
  eSubstV  : {var : cpstyp → Set} {τ₁ τ : typ} →
             {v₁ : var (cpsT τ) → value[ var ∘ cpsT ] τ₁} →
             {v₁′ : value[ var ∘ cpsT ] τ₁} →
             {v : value[ var ∘ cpsT ] τ} →
             SubstVal v₁ v v₁′ →
             cpsSubstVal (λ y → cpsV {var = var} (v₁ y)) (cpsV v) (cpsV v₁′)
             
  eSubstV SubstVal.sVar= = cpsSubstVal.sVar=
  eSubstV SubstVal.sVar≠ = cpsSubstVal.sVar≠
  eSubstV SubstVal.sNum = cpsSubstVal.sNum
  eSubstV (sFun sub) = sFun (λ x → sVal (sFun (λ k → sVal (sFun (λ x₁ →
                       ekSubst' (λ x₂ x₃ → _) (CPSVar x₁) (sub x))))))

  eSubst   : {var : cpstyp → Set} {τ₁ α β τ : typ} {μα μβ : trail} →
             {e₁ : var (cpsT τ) →
               term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             {t :  cpsvalue[ var ] cpsM μβ} →
             {trail : cpsvalue[ var ] cpsM μα} →
             Subst e₁ v e₂ →
             subst-cont (λ x → k) (cpsV v) k →
             cpsSubst (λ x → cpsTerm (e₁ x) k t) (cpsV v)
             (cpsTerm e₂ k t)

  eSubst {v = v}{k = k}{trail = trail} (sVal x) eq = {!!}
  eSubst (sApp x x₂) eq = {!!}
  eSubst (sPlu x x₂) x₁ = {!!}
  eSubst (sCon x) x₁ = {!!}
  eSubst (sPro x) x₁ = {!!}

  kSubst : {var : cpstyp → Set}{τ₁ α β : typ} {μα μβ : trail} {τ : cpstyp} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] τ} →
           (k₁ : var τ →
                  cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
           {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
           {t₁ : cpsvalue[ var ] (cpsM μβ)} →
           subst-cont k₁ v k₂ →
           cpsSubst (λ x → cpsTerm e (k₁ x) t₁) v (cpsTerm e k₂ t₁)

  kSubst = {!!}

  tSubst : {var : cpstyp → Set}{τ₁ τ₂ α β : typ} {μα μβ : trail} {τ : cpstyp} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] τ} →
           (t₁ : var τ → cpsvalue[ var ] (cpsM μβ)) →
           {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
           (t₂ : cpsvalue[ var ] (cpsM μβ)) →
           --subst-trail {τ₁ = τ₁}{τ₂ = τ₂} t₁ v t₂ →
           cpsSubst (λ x → cpsTerm e k (t₁ x)) v (cpsTerm e k t₂)

  tSubst = {!!}


  ekSubst  : {var : cpstyp → Set} {τ τ₁ α β : typ} {μα μβ : trail} →
             {e₁ : (var ∘ cpsT) τ → term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k₁ : var (cpsT τ) → cpsvalue[ var ] (cpsT τ₁) →
              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             {k₂ : cpsvalue[ var ] (cpsT τ₁) →
              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             {t₁ : cpsvalue[ var ] (cpsM μβ)} →
             Subst e₁ v e₂ →
             subst-cont k₁ (cpsV v) k₂ →
             cpsSubst (λ y → cpsTerm (e₁ y) (k₁ y) t₁) (cpsV v)
                     (cpsTerm e₂ k₂ t₁)

  ekSubst (sVal x) eq = {!!}
  -- eq Subst≠ (eSubstV x)
  ekSubst (sApp sub₁ sub₂) eq = {!!}
  -- ekSubst sub₁
                                --   λ m n → ekSubst {!sub₂!}
                                --   λ m₂ n₂ → sApp (sApp (sVal {!n!}) (sVal n₂))
                                --   (sVal (sFun (λ x → eq (sVal {!n₂!}) sVar≠)))
  ekSubst (sPlu x x₂) eq = ekSubst x {!eq!}
  ekSubst (sCon x) x₁ = {!!}
  ekSubst (sPro x) x₁ = {!!}


-- ([e₁]′ @ k)[v/y] = [e₂]′ @ k
  ekSubst'  : {var : cpstyp → Set} {τ₁ τ α β : typ} {μα μβ : trail} →
              {e₁ : var (cpsT τ) →
                    term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
              {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
              {v : value[ var ∘ cpsT ] τ} →
              (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) →
              cpsterm[ var ] (cpsT α)) →
              (t : cpsvalue[ var ] (cpsM μβ)) →
              Subst e₁ v e₂ →
              cpsSubst (λ x → cpsTerm (e₁ x) k t)
                      (cpsV v)
                      (cpsTerm e₂ k t)

  ekSubst' k t (sVal sub) = {!!}
  ekSubst' k t (sApp sub₁ sub₂) = {!!}
  ekSubst' k t (sPlu x x₁) = {!!}
  ekSubst' k t (sCon x) = {!!}
  ekSubst' k t (sPro x) = {!!}

  schematicV : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
             (k : cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
             (t : cpsvalue[ var ] cpsM μα) → Set
             
  schematicV {var} {τ₁} k t =
             (v : value[ var ∘ cpsT ] τ₁) →
             cpsSubst (λ x → k (CPSVar x) t) (cpsV v) (k (cpsV v) t)
  
schematic : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
            (k : cpsvalue[ var ] (cpsT τ₁) →
                 cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
            (t : cpsvalue[ var ] cpsM μα) → Set
schematic {var} {τ₁} k  t =
  (v : cpsvalue[ var ] (cpsT τ₁)) →
  cpsSubst (λ x → k (CPSVar x) t) v (k v t)



correctEta : {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail} →
             {e e′ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
             (t : cpsvalue[ var ] (cpsM μβ)) →
             (t′ : cpsvalue[ var ] (cpsM μα)) →
             schematicV {var} {τ₁} {α} {μα} k t′ →
             Reduce e e′ →
             cpsreduce (cpsTerm e k t) (cpsTerm e′ k t)   --⟦ e ⟧k = ⟦ e′ ⟧k

correctEta {e′ = e′} k t t' sch (RBeta {e₁ = e₁} {v₂ = v₂} x) = begin
  (cpsTerm (App (Val (Fun e₁)) (Val v₂)) k t)
  ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₁ → sVal (sFun (λ x₂ → eSubst x λ x₃ x₄ → sApp (sApp Subst≠ (sVal SubstV≠)) Subst≠))))))) ⟩
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
  ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → kSubst e′
                                          (λ y v t'' →
                                             CPSApp (CPSApp (CPSVal (CPSVar y)) (CPSVal v)) (CPSVal t''))
                                          (λ x₂ x₃ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))) ⟩
                                          
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
  ⟶⟨ rBeta (tSubst {!e′!} (λ x₁ → CPSVar x₁) t) ⟩
  (cpsTerm e′ k t)
  ∎
correctEta k t t' sch (RPlus {τ₂} {μα} {n₁} {n₂}) = begin
  (CPSLet (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂))) (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rPlus ⟩
  CPSLet (CPSVal (CPSNum (n₁ + n₂))) (λ v → k (CPSVar v) t)
  ⟶⟨ rLet {!!} ⟩
  k (CPSNum (n₁ + n₂)) t
  ∎
  -- (k (CPSNum (n₁ + n₂)) t)

  -- cpsreduce* (cpsTerm (frame-plug f e₁) k t)
  --     (cpsTerm (frame-plug f e₂) k t)

correctEta k t t' sch (RFrame  (App₁ e₃) x) = correctEta (λ v₁ →
                                                      cpsTerm e₃
                                                      (λ v₂ t₂ →
                                                         CPSApp
                                                         (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                                          (CPSVal
                                                           (CPSFun
                                                            (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
                                                         (CPSVal t₂))) t {!!} {!sch!} x
correctEta k t t' sch (RFrame (App₂ v₁) x) = correctEta (λ v₂ t₂ →
                                                     CPSApp
                                                     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (CPSVal
                                                       (CPSFun
                                                        (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
                                                     (CPSVal t₂)) t {!!} {!!} x
correctEta k t t' sch (RFrame (Plus₁ e₃) x) = correctEta (λ v₁ →  cpsTerm e₃
                                                                          (λ v₂ t₂ →
                                                                             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k (CPSVar v) t₂))) t {!!} {!!} x
correctEta k t t' sch (RFrame (Plus₂ v₁) x) = correctEta (λ v₂ t₂ →
                                                      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (λ v → k (CPSVar v) t₂)) t {!!} {!!} x
correctEta k t t' sch (RFrame {e₁ = e₁} {e₂ = e₂} (Pro x₁) x) = begin
  (CPSLet (cpsTerm e₁ (CPSIdk x₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ (correctEta (CPSIdk x₁) (CPSId) {!!} {!sch!} x) ⟩
  (CPSLet (cpsTerm e₂ (CPSIdk x₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ∎
  
correctEta k t t' sch (RPrompt {v₁ = v₁}) = begin
  (CPSLet (CPSIdk refl (cpsV v₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rIdkid ⟩
  CPSLet (CPSVal (cpsV v₁)) (λ v → k (CPSVar v) t)
  ⟶⟨ rLetApp ⟩
  CPSApp (CPSVal (CPSFun (λ v → k (CPSVar v) t))) (CPSVal (cpsV v₁))
  ⟶⟨ rBeta {!sch v !} ⟩
  (k (cpsV v₁) t)
  ∎
correctEta k t t' sch (RControl p₁ p₂ x₁ x₂ x₃ x e) = {!!}



