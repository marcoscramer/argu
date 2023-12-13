package body Input_Output with
   Spark_Mode
is


   -- Convert AF from graph representation to adjacency matrix representation:
   function AF_From_Graph (G : AF_Graph) return AF is
      N : Natural := 0;
      M : Natural;
      AM : BoolMatrix := (1 .. MaxNumberOfArgs => (1 .. MaxNumberOfArgs => False));
      F : AF;
   begin

      for I in G'Range loop
         pragma Loop_Invariant (for all J in G'First .. I-1 => G(J)(1) <= N and G(J)(2) <= N and AM(G(J)(1),G(J)(2)));
         pragma Loop_Invariant (N <= MaxNumberOfArgs);
         pragma Loop_Invariant (for all K in 1 .. MaxNumberOfArgs => (for all J in 1 .. MaxNumberOfArgs => (if K > N or J > N then not AM(K,J))));
         pragma Loop_Invariant (for all a in 1 .. MaxNumberOfArgs => (for all b in 1 .. MaxNumberOfArgs => (if AM(a,b) then (for some J in G'Range => a = G(J)(1) and b = G(J)(2)))));
         M := Positive'Max(G(I)(1),G(I)(2));
         N := Positive'Max(M,N);
         AM(G(I)(1),G(I)(2)) := True;
      end loop;

      F := AF'(Size => N, AdjacencyMatrix => AM);
      return F;

   end AF_From_Graph;


   function ArgList_From_ArgSet (S : ArgSet; F : AF) return ArgList is
      L : NatArray := (1 .. MaxNumberOfArgs => 0);
      OldL : NatArray;
      Counter : Natural := 0;
      OldCounter : Natural;
   begin

      for I in 1 .. F.Size loop
         pragma Loop_Invariant (Counter < I);
         pragma Loop_Invariant (Counter < F.Size);
         pragma Loop_Invariant (for all K in I .. MaxNumberOfArgs => not (for some J in 1 .. Counter => L(J) = K));
         pragma Loop_Invariant (for all K in 1 .. I-1 => (if S(K) then (for some J in 1 .. Counter => L(J) = K)));
         pragma Loop_Invariant (for all K in 1 .. I-1 => (if (for some J in 1 .. Counter => L(J) = K) then S(K)));
         pragma Loop_Invariant (for all K in 1 .. Counter => (L(K) /= 0 and not (for some J in 1 .. Counter => (J /= K and L(J) = L(K)))));
         pragma Loop_Invariant (for all K in Counter+1 .. MaxNumberOfArgs => L(K) = 0);
         OldCounter := Counter;
         OldL := L;
         if S(I) then
            Counter := Counter+1;
            L(Counter) := I;
            Exist_Intro_L(I,Counter,L);
         end if;
         Extend_Quantification_Ranges(I,Counter,OldCounter,S,L,OldL,F);
         pragma Assert (if S(I) then (for some J in 1 .. MaxNumberOfArgs => L(J) = I));
      end loop;

      return ArgList'(Size => Counter, List => L);

   end ArgList_From_ArgSet;


   function ArgSet_From_InputArgList (L : InputArgList; N : AFSize) return ArgSet is
      S : ArgSet := (1 .. MaxNumberOfArgs => False);
   begin

      for K in L'Range loop
         pragma Loop_Invariant (for all I in 1 .. N => (if S(I) then (for some J in L'First .. K-1 => L(J) = I)));
         pragma Loop_Invariant (for all I in 1 .. N => (if (for some J in L'First .. K-1 => L(J) = I) then S(I)));
         S(L(K)) := True;
      end loop;
      return S;

   end ArgSet_From_InputArgList;


   function Grounded_Input_Output (G : AF_Graph) return ArgList is
      F : AF := AF_From_Graph(G);
   begin

      return ArgList_From_ArgSet(Core_Functions_And_Theorems.Find_Grounded(F),F);

   end Grounded_Input_Output;


   function Check_Grounded_Input_Output (G : AF_Graph; L : InputArgList) return Boolean is
      F : AF := AF_From_Graph(G);
   begin

      return (ArgSet_From_InputArgList(L,F.Size) = Find_Grounded(F));

   end Check_Grounded_Input_Output;


   procedure Extend_Quantification_Ranges (I : Natural; Counter : Natural; OldCounter : Natural; S : ArgSet; L : NatArray; OldL : NatArray; F : AF) is
   begin
         for K in 1 .. I-1 loop
            pragma Loop_Invariant (for all M in 1 .. K-1 => (if S(M) then (for some J in 1 .. Counter => L(J) = M)));
            if S(K) then
               pragma Assert (for some J in 1 .. Counter => L(J) = K);
            end if;
         end loop;
   end Extend_Quantification_Ranges;


   procedure Exist_Intro_L (I : Natural; Counter : Natural; L : NatArray) is
   begin
      null;
   end Exist_Intro_L;


   procedure Print_ArgList (L : in ArgList) is
      -- S : String := Integer'Image(0);
   begin
   Ada.Text_IO.Put("Grounded extension: {");
   for I in 1 .. L.Size loop
      declare
         S : String := Integer'Image(L.List(I));
      begin
         Ada.Text_IO.Put(S(2 .. S'Length));
      end;
      if I < L.Size then
         Ada.Text_IO.Put(", ");
      end if;
   end loop;
   Ada.Text_IO.Put("}");
   Ada.Text_IO.New_Line;
   end Print_ArgList;


end Input_Output;
