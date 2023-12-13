package body Counting with
   Spark_Mode
is


   procedure ArgList_Not_Full (L : ArgList; N : AFSize) is
      A : NatArray := (1 .. MaxNumberOfArgs => 0);
   begin

      for I in 1 .. N loop
         pragma Loop_Invariant (for all J in 1 .. I-1 => A(J) = J);
         A(I) := I;
      end loop;
      Quantified_Substitution_Of_Equals(A,N,L);
      for J in 1 .. N loop
         pragma Loop_Invariant (for all K in 1 .. J-1 => Array_Contains(A,N,K));
         pragma Assert (A(J) = J);
         pragma Assert (Array_Contains(A,N,J));
      end loop;
      pragma Assert (for all J in 1 .. N => Array_Contains(A,N,J));
      pragma Assert (for all J in 1 .. L.Size => Array_Contains(A,N,L.List(J)));
      for I in 1 .. L.Size loop
         pragma Loop_Invariant (for all J in 1 .. N-I+1 => A(J) in 1 .. N);
         pragma Loop_Invariant (for some J in 1 .. N-I+1 => not ArgSet_From_ArgList(L,N)(A(J)));
         pragma Loop_Invariant (for all J in I .. L.Size => Array_Contains(A,N-I+1,L.List(J)));
         Remove_Elt_From_Array(L.List(I),A,N,N-I+1);
      end loop;

   end ArgList_Not_Full;


   procedure Quantified_Substitution_Of_Equals (A : NatArray; N : AFSize; L : ArgList) is
   begin

      if (for all J in 1 .. N => ArgSet_From_ArgList(L,N)(A(J))) then
         for J in 1 .. N loop
            pragma Loop_Invariant (for all I in 1 .. J-1 => ArgSet_From_ArgList(L,N)(I));
            Substitution_Of_Equals(A,J,N,L);
         end loop;
         pragma Assert (for all J in 1 .. N => ArgSet_From_ArgList(L,N)(J));
      end if;

   end;


   procedure Substitution_Of_Equals (A : NatArray; J : Natural; N : AFSize; L : ArgList) is
   begin
      null;
   end;


   procedure Remove_Elt_From_Array (b : Arg; A : in out NatArray; N : Natural; K : Natural) is
      Found : Boolean := False; -- whether b has already been found in A
      Position : Natural := 0; -- position where b was found in A
      AOld : NatArray := A;
   begin

      for I in 1 .. K loop
         pragma Loop_Invariant (for all J in 1 .. K => A(J) in 1 .. N);
         pragma Loop_Invariant (if not Found then A = AOld);
         pragma Loop_Invariant (if Found then Position in 1 .. I-1 and AOld(Position) = b and (for all J in 1 .. Position-1 => A(J) = AOld(J)) and (for all J in Position .. I-1 => A(J) = AOld(J+1)));
         pragma Loop_Invariant (if not Found then (for some J in I .. K => A(J) = b));
         if Found = False then
            if A(I) = b then
               Found := True;
               Position := I;
               if I < K then
                  A(I) := A(I+1);
               end if;
            end if;
         end if;
         if Found = True then
            if I < K then
               A(I) := A(I+1);
            end if;
         end if;
      end loop;

      pragma Assert (for all J in 1 .. K-1 => A(J) in 1 .. N);
      pragma Assert (for all J in 1 .. N => (if J /= b then (for all I in 1 .. Position-1 => (if AOld(I) = J then A(I) = J)) and (for all I in Position .. K-1 => (if AOld(I+1) = J then A(I) = J))));
      for J in 1 .. N loop
         pragma Loop_Invariant (for all M in 1 .. J-1 => (if M /= b and (for some I in 1 .. K => AOld(I) = M) then (for some I in 1 .. K-1 => A(I) = M)));
         for I in 1 .. K loop
            pragma Loop_Invariant (for all M in 1 .. I-1 => (if J /= b and AOld(M) = J then (for some P in 1 .. K-1 => A(P) = J)));
            if J /= b and AOld(I) = J then
               pragma Assert (I /= Position);
               if I < Position then
                  pragma Assert (A(I) = J);
               else
                  pragma Assert (A(I-1) = J);
               end if;
               pragma Assert (for some P in 1 .. K-1 => A(P) = J);
            end if;
         end loop;
         pragma Assert (if J /= b and (for some P in 1 .. K => AOld(P) = J) then (for some P in 1 .. K-1 => A(P) = J));
      end loop;

      pragma Assert (for all J in 1 .. N => (if J /= b and (for some I in 1 .. K => AOld(I) = J) then (for some I in 1 .. K-1 => A(I) = J)));

   end Remove_Elt_From_Array;


end Counting;
