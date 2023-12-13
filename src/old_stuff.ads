
   type NaturalPair is array (Positive range 1 .. 2) of Natural;

   procedure Quantificational_Reasoning (N : AFSize; L1 : ArgList; L2 : ArgList) with
     Ghost,
     Pre => (N < MaxNumberOfArgs; Is_ArgList_For(L1,N+1) and then (for some a in 1 .. N => not ArgSet_From_ArgList(L1,N+1)(a)) and then (for all a in 1 .. N => (if (for all K in 1 .. N+1 => L1.List(K) /= a) then (for all K in 1 .. N => L2.List(K) /= a)))),
     Post => (for some a in 1 .. N => not ArgSet_From_ArgList(L2,N)(a));

   procedure Superset_Defends (S1 : ArgSet; S2 : ArgSet; a : Arg; F : AF) with
     Ghost,
     Pre => (Is_ArgSet(S1,F.Size) and then Is_ArgSet(S2,F.Size) and then Subset(S1,S2) and then a <= F.Size and then Defends(S1,a,F)),
     Post => (Defends(S2,a,F));


   function ArgSet_Up_To (S : ArgSet; N : AFSize) return ArgSet with
     Post => ((for all I in 1 .. N => (if S(I) then ArgSet_Up_To'Result(I))) and then (for all I in N+1 .. MaxNumberOfArgs => not ArgSet_Up_To'Result(I)) and then (for all I in 1 .. MaxNumberOfArgs => (if ArgSet_Up_To'Result(I) then S(I))));

   function ArgSet_Size_Comparison (S1 : ArgSet; S2 : ArgSet) return NaturalPair with
     Pre => (Subset(S1,S2)),
     Post => (ArgSet_Size_Comparison'Result(1) <= ArgSet_Size_Comparison'Result(2) and then (if S1 /= S2 then ArgSet_Size_Comparison'Result(1) < ArgSet_Size_Comparison'Result(2)));


   procedure ArgSets_Up_To_0_Identical (S1 : ArgSet; S2 : ArgSet) with
     Ghost,
     Post => (ArgSet_Up_To(S1,0) = ArgSet_Up_To(S2,0));

   procedure ArgSets_Up_To_Identity_Induction_Step (S1 : ArgSet; S2 : ArgSet; N : Positive) with
     Ghost,
     Pre => (N <= MaxNumberOfArgs and then ArgSet_Up_To(S1,N-1) = ArgSet_Up_To(S2,N-1) and then S1(N) = S2(N)),
     Post => (ArgSet_Up_To(S1,N) = ArgSet_Up_To(S2,N));
