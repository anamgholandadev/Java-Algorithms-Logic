package com.thealgorithms.strings;

/* In information theory, the Hamming distance between two strings of equal length
is the number of positions at which the corresponding symbols are different.
https://en.wikipedia.org/wiki/Hamming_distance
*/
public class HammingDistance {

    /**
     * calculate the hamming distance between two strings of equal length
     *
     * @param s1 the first string
     * @param s2 the second string
     * @return {@code int} hamming distance
     * @throws Exception
     */

    //@ public static ghost int[] g_different_arr = new int[1];

    //@   public normal_behaviour
    //@     requires s1 != null && s2 != null; 
    //@     requires s1.length() == s2.length();
    //@     requires s1.length() < Integer.MAX_VALUE; 
    //@     assigns g_different_arr;
    //@     ensures 0 <= \result <= s1.length(); 
    //@     ensures g_different_arr.length == s1.length()+1;
    //@     ensures g_different_arr[0] == 0;
    //@     ensures \forall int k; 1 <= k <= s1.length();
    //@                 s1.charAt(k-1) != s2.charAt(k-1) ==> g_different_arr[k] == g_different_arr[k-1] + 1;
    //@     ensures \forall int k; 1 <= k <= s1.length();
    //@                 s1.charAt(k-1) == s2.charAt(k-1) ==> g_different_arr[k] == g_different_arr[k-1];
    //@     ensures \result == g_different_arr[s1.length()];
    //@ also
    //@   public exceptional_behavior
    //@     requires s1.length() != s2.length();
    //@     signals_only Exception;
    public static int calculateHammingDistance(String s1, String s2) throws Exception {
        if (s1.length() != s2.length()) {
            throw new Exception("String lengths must be equal");
        }
        //@ assert s1.length() == s2.length();

        //@ set g_different_arr = new int[s1.length()+1];
        //@ set g_different_arr[0] = 0;

        int stringLength = s1.length();
        int counter = 0;
        //@ assert counter == 0;

        //@ maintaining 0 <= i <= s1.length();
        //@ maintaining counter < Integer.MAX_VALUE;
        //@ loop_writes counter, g_different_arr[1..s1.length()];
        //@ maintaining \forall int k; 1 <= k <= i;
        //@                 s1.charAt(k-1) != s2.charAt(k-1) ==> g_different_arr[k] == g_different_arr[k-1] + 1;
        //@ maintaining \forall int k; 1 <= k <= i;
        //@                 s1.charAt(k-1) == s2.charAt(k-1) ==> g_different_arr[k] == g_different_arr[k-1];
        //@ maintaining counter == g_different_arr[i];
        //@ maintaining 0 <= counter <= i;
        //@ decreases s1.length() - i;
        for (int i = 0; i < stringLength; i++) {
            if (s1.charAt(i) != s2.charAt(i)) {
                // @ assume 0 <= counter+1 < Integer.MAX_VALUE;
                counter++;
                //@ set g_different_arr[i+1] = g_different_arr[i] + 1;
            } else{
                //@ set g_different_arr[i+1] = g_different_arr[i];
            }

        }

        //@ assert \forall int k; 1 <= k <= s1.length(); s1.charAt(k-1) != s2.charAt(k-1) ==> g_different_arr[k] == g_different_arr[k-1] + 1;
        //@ assert \forall int k; 1 <= k <= s1.length(); s1.charAt(k-1) == s2.charAt(k-1) ==> g_different_arr[k] == g_different_arr[k-1]; 

        return counter;
    }
}
