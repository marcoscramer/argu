with Types; use Types;
with Aux; use Aux;
with Core_Definitions; use Core_Definitions;
with Core_Functions_And_Theorems; use Core_Functions_And_Theorems;
with Ada.Text_IO; use Ada.Text_IO;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;

package Input_Output with
   Spark_Mode
is


   function AF_From_Graph (G : AF_Graph) return AF with
     Post => (for all I in G'Range => G(I)(1) <= AF_From_Graph'Result.Size and then
                G(I)(2) <= AF_From_Graph'Result.Size and then
                Attacks(G(I)(1),G(I)(2),AF_From_Graph'Result)) and then
             (for all a in 1 .. AF_From_Graph'Result.Size => (for all b in 1 .. AF_From_Graph'Result.Size =>
                (if Attacks(a,b,AF_From_Graph'Result) then (for some I in G'Range => a = G(I)(1) and b = G(I)(2)))));

   function ArgList_From_ArgSet (S : ArgSet; F : AF) return ArgList with
     Pre => Is_ArgSet(S,F.Size),
     Post => ArgList_From_ArgSet'Result.Size <= F.Size and then
     (for all I in 1 .. F.Size => not (S(I) xor (for some J in 1 .. ArgList_From_ArgSet'Result.Size => ArgList_From_ArgSet'Result.List(J) = I)));

   function ArgSet_From_InputArgList (L : InputArgList ; N : AFSize)  return ArgSet with
     Pre => L'Last <= MaxNumberOfArgs,
     Post => --Is_ArgSet(ArgSet_From_InputArgList'Result,N) and then
             (for all I in 1 .. N => not (ArgSet_From_InputArgList'Result(I) xor (for some J in L'Range => L(J) = I)));


   function Grounded_Input_Output (G : AF_Graph) return ArgList with
     Post => Grounded_Input_Output'Result = (ArgList_From_ArgSet(Find_Grounded(AF_From_Graph(G)),AF_From_Graph(G)));

   function Check_Grounded_Input_Output (G : AF_Graph; L : InputArgList) return Boolean with
     Pre => L'Last <= MaxNumberOfArgs,
     Post => Check_Grounded_Input_Output'Result = (ArgSet_From_InputArgList(L,AF_From_Graph(G).Size) = Find_Grounded(AF_From_Graph(G)));


   procedure Extend_Quantification_Ranges (I : Natural; Counter : Natural; OldCounter : Natural; S : ArgSet; L : NatArray; OldL : NatArray; F : AF) with
     Ghost,
     Pre => I <= F.Size and then
            OldCounter <= Counter and then
            Counter <= MaxNumberOfArgs and then
            (for all K in 1 .. I-1 => (if S(K) then (for some J in 1 .. OldCounter => OldL(J) = K))) and then
            (for all J in 1 .. OldCounter => L(J) = OldL(J)),
     Post => (for all K in 1 .. I-1 => (if S(K) then (for some J in 1 .. Counter => L(J) = K)));

   procedure Exist_Intro_L (I : Natural; Counter : Natural; L : NatArray) with
     Ghost,
     Pre => Counter in 1 .. MaxNumberOfArgs and then L(Counter) = I,
     Post => (for some J in 1 .. Counter => L(J) = I);


   procedure Print_ArgList (L : in ArgList);

   function Singleton (a : Arg) return InputArgList is
      (1 .. 1 => a);


end Input_Output;
