// The Prisoner of Benda
//
// Professor Farnsworth's mind-switching machine has been used unwittingly by
// the crew to switch minds.
// Unfortunately, the machine can switch minds between any pair of bodies only
// once. Can everyone be 
// switched back if we use more bodies? Oh dear, I am afraid we will have to use
// ... math!
// 
// Good news everyone! The Harlem Globetrotters have devised a method to switch
// everyone
// back using only two extra bodies! Let's get on with it then.
//
// The array L represents a permutation of the minds of the crew, where index i
// is body i and contains mind L[i]. Without loss 
// of generality (since an invertable data transformer exists for any list),
// assume that minds and bodies are numbered 0 through 
// L.Length. So originally body i had mind i.
//
// Prove that the following algorithm correctly switches everyone back,
// including the two extra bodies.
//
method benda(L:array<int>, v0:int, v1:int) returns (x:int, y:int)
	requires L != null;
	requires forall i::0 <= i < L.Length ==> 0 <= L[i] < L.Length; //in range
	requires forall i,j::0 <= i < j < L.Length ==> L[i] != L[j]; //distinct
	requires v0 !in L[..] && v1 !in L[..] && v0 != v1;
	modifies L; 
	ensures forall j::0 <= j < L.Length ==> L[j] == j; //everyone is switched back
	ensures x == v0 && y == v1; //extras are also switched back
{
	var i;
	i,x,y := 0,v0,v1;
	while (i < L.Length)
		invariant 0 <= i <= L.Length;
		invariant forall j::i <= j < L.Length ==> i <= L[j] < L.Length; // in range
		invariant forall j,k::i <= j < k < L.Length ==> L[j] != L[k]; //distinct
		invariant forall j::0 <= j < i ==> L[j] == j; //minds returned
		invariant {x,y} == {v0,v1}; //extra bodies have the extra minds
	{
		if (L[i] != i) {    
			x,L[i] := L[i],x;

			x := cycle(L,i,x,(set z | i < z < L.Length && L[z] != z));
				y,L[x] := L[x],y;
				x,L[x] := L[x],x;
				y,L[i] := L[i],y;      
		}

		i := i+1;
	}

	// if the two extras are switched at the end, switch back
	if (x != v0) {
		x,y := y,x;
	} 
}

method cycle(L:array<int>, i:int, a:int, s:set<int>) returns (x:int)
	requires L!=null;
	requires 0 <= i < a < L.Length; //a is in range
	requires forall j::i < j < L.Length ==> i <= L[j] < L.Length; //in range after i
	requires forall j::i < j < L.Length ==> L[j] != a; //after i all elements distinct (including a)
	requires forall j,k::i < j < k < L.Length ==> L[j] != L[k]; //distinct
	requires s == (set z | i < z < L.Length && L[z] != z); //the termination measure
	modifies L;
	decreases s;
	ensures forall j::0 <= j <= i ==> L[j] == old(L[j]); //before index i, nothing changed
	ensures forall j::i < j < L.Length ==> i <= L[j] < L.Length; //in range after i
	ensures forall j::i < j < L.Length ==> L[j] != x; //after i all elements distinct (including x)
	ensures forall j,k::i < j < k < L.Length ==> L[j] != L[k]; //distinct
	ensures i <= x < L.Length; //x in range
	ensures L[x] == i;
{
	x := a;
	if (L[x] != i) {
		x,L[x] := L[x],x;

		x:=cycle(L,i,x,s-{a});
	}
}

method Main(){
	var a:= new int[5];
	a[0],a[1],a[2],a[3],a[4]:= 3,2,1,4,0;
	var x,y:= benda(a, a.Length, a.Length + 1);
	print a[..]," ",x," ",y,"\n";
}
