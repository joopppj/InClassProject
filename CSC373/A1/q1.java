package A1;
public class q1{
	public static int q1(int[] a){
		if(a[0]==Integer.MAX_VALUE)return 0;
		int up=Integer.MAX_VALUE;
		int low=1;
		while(up>=low){
			if(up==Integer.MAX_VALUE){
				for(int i=1;;){
					if(a[i]<Integer.MAX_VALUE){low=i;i*=2;}
					else {up=i;i++;}
					System.out.println(i);
					System.out.println(up);
					System.out.println(low);
				}
			}
			if(up==Integer.MAX_VALUE)return Integer.MAX_VALUE;
			
			int mid= (low+up)/2;
			if(a[mid]<Integer.MAX_VALUE&&a[mid+1]==Integer.MAX_VALUE)return mid+1;
			if(a[mid]==Integer.MAX_VALUE)up=mid-1;
			if(a[mid]<Integer.MAX_VALUE)low=mid+1;	
		}
		return 0;
	}
	public static void main(String[] args){
		System.out.println(q1(new int[]{1,1,2,Integer.MAX_VALUE} ));
	}
}