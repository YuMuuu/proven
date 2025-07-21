import Init.Data.Nat.Basic
import Mathlib.Data.List.Chain
import Mathlib.Order.Basic


-- @see [[https://dl.acm.org/doi/pdf/10.1145/38713.38760]]
-- LOGICAL MODELING OF TEMPORALDATA という論文の仕様検証


/-- Temporal Data Value
時系列データ値　オブジェクト識別値としてのサロゲート、時刻、属性値を持つ
同一サロゲートに属するデータ値は、時間に沿って全順序を持つ。 <- この制約はTDVじゃなくてTS側の制約では？
⟨s,t,a⟩　と表記する 非時系列データの場合はtは現在時刻として省略される
-/
structure TDV (S : Type u) (T : Type w) (A : Type v) [LinearOrder T] where
  s: S
  t: T
  a: A

/-- Time Stamp
特定のオブジェクトに対応する、順序付きの時系列データ値の集まり。

⟨s,(t,a)∗⟩ と表記する　(t,a)^* は時刻と値のペアの列。
-/
structure TS (S : Type u) (T : Type w ) (A : Type v) [LinearOrder T] where
  s: S
  pairs: List (T × A)
  sorted  : pairs.Chain' (fun p q => p.fst < q.fst) -- 時刻が厳密昇順　
  -- ※これはTDVの仕様だが、同一サロゲートに属する, a はTSでしか表せないためこちらで定義する

inductive TSType where
  | StepWiseConstant -- ステップ定数型
  | Continuous -- 連続型
  | Discrete -- 離散型
  | UserDefinedTypeMissingValue --　ユーザ定義型欠損値

/-- Object
オブジェクトはサロゲートとアトリビュートを持つ
-/
structure Obj (S : Type v) (A : Type w) where
  surr : S
  attrs : A

/-- Objects 上での単射性 -/
def InjOn {α : Type u} {β : Type v} (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x y⦄, x ∈ s → y ∈ s → f x = f y → x = y

/-- Class
  一意のサロゲートを持つ Object の集合を持つ
-/
structure Clazz (S : Type v) (A : Type w) where
  objects      : Set (Obj S A)
  surr_inj     : InjOn (fun o => o.surr) objects  -- 集合上でサロゲートが一意

-- /-- 時系列コレクションの分類 -/
inductive TSCType where
  | discrete          -- 離散的な時点でのみ値が存在
  | stepwise_constant -- 変更されるまで値が一定
  | continuous        -- 時間全体で連続的に値が定義される


/-- 単純なTSC
単純クラスかつ単一の時間ドメイン T・属性ドメイン A に対し、サロゲートに一つのTS を対応させる写像。
-/
structure SimpleTSC
  (S : Type u) (T : Type w) (A : Type v) (C : Clazz S A) [LinearOrder T] where
  ts   : { o : Obj S A // o ∈ C.objects } → TS S T A
  s_ok : ∀ (o : { o : Obj S A // o ∈ C.objects }), (ts o).s = o.val.surr
  -- （この時点では）SimpleTSCもComplexTSCもTSCの単なる特殊化であり例えばSが S1なのか S1 x S2 なのかの違いしかない


 /--
 時系列測定の精度と単位の定義
 粒度階層：秒 < 分 < 時 < 日 < 月 < 年
 TODO: この定義だと時間を正数の順序で表したりカレンダーの階層構造を表すことができていない。
 必要になったら真面目に実装する
  -/
inductive TimeGranularity where
  | second
  | minute
  | hour
  | day
  | month
  | year

/--
寿命

fixed, endpoint=now, startpoint=endpoint-distance　かつ endpont=currenttime みたいな表現が可能
-/
structure Lifespan (T : Type v) [LinearOrder T] where
  start_point : T
  end_point : T
  valid : start_point < end_point


inductive Regularity where
  | regular    -- 規則的な時系列間隔
  | irregular  -- 規則的でない時系列間隔


/-- Time Stamp Collection
同じクラス（または型）に属するオブジェクトの時系列オブジェクトのコレクション
論文ではTSCType、TimeGranularity、Lifespan、Regularityも構成要素に含まれているが、TSCのインスタンス生成やオペレータの定義には不要なので追加していない
-/
structure TSC
  (S : Type u) (T : Type w) (A : Type v) (C : Clazz S A) [LinearOrder T] where
  ts   : { o : Obj S A // o ∈ C.objects } → TS S T A
  s_ok : ∀ (o : { o : Obj S A // o ∈ C.objects }), (ts o).s = o.val.surr

-- complex TSC
-- Tが単一の要素でない場合は、時間的な値が複数の時間シーケンスに関連付けられている状態に対応する
-- 例えば transaction timeとvalid timeを持つ

variable {T : Type v} [LinearOrder T]

-- ある時刻tがlifeSpanの閉区間に存在する
def contains (L : Lifespan T) (t : T) : Prop :=
  L.start_point ≤ t ∧ t ≤ L.end_point

-- TS のすべてのタイムスタンプが寿命 `L` に内包される（= TS が L を満たす)
def respects (ts : TS S T A) (L : Lifespan T) : Prop :=
  ∀ {t a}, (t, a) ∈ ts.pairs → contains L t

-- ある時刻tがTS上の観測地点として現れる
def hasTime (ts : TS S T A) (t : T) : Prop :=
  ∃ a, (t, a) ∈ ts.pairs

-- あるTSの全ての観測地点はLifespanの閉空間に存在する
def supportedWithin (ts : TS S T A) (L : Lifespan T) : Prop :=
  ∀ {t a}, (t, a) ∈ ts.pairs → L.start_point ≤ t ∧ t ≤ L.end_point


abbrev AccountNo := String --明記されていないが簡単に実装するために口座番号をサロゲートキーとする

structure BankAttrs where
  balance : Int

def obj1 : Obj Nat Nat := { surr := 1, attrs := 57 }

abbrev BankClazzVal : Clazz Nat Nat :=
  { objects :=  ({obj1} : Set (Obj Nat Nat)),
    surr_inj := by
      intro x y hx hy hxy
      have hx' : x = obj1 := hx
      have hy' : y = obj1 := hy
      rw [hx', hy'] }

-- サンプルにある口座残高の推移の例
-- - 1日目: 残高 = ¥57
-- - 4日目: 残高 = ¥50
-- - 6日目: 残高 = ¥65
-- - 9日目: 残高 = ¥60
example : TSC Nat Nat Nat BankClazzVal :=
  { ts := fun o =>
    { s := o.val.surr,
      pairs := [(1, 57), (4, 50), (6, 65), (9, 60)],
      sorted := by decide
    },
    s_ok := by intros; rfl }

    
