package com.thealgorithms.maths;

public final class Factorial {
    private Factorial() {
    }

    //@ public static ghost int[] g_factorial_arr = new int[1];

    /**
     * Calculate factorial N using iteration
     *
     * @param n the number
     * @return the factorial of {@code n}
     */
    //@   public normal_behavior
    //@     requires 0 <= n < 12;
    //@     assigns g_factorial_arr;
    //@     ensures g_factorial_arr.length == n+1;
    //@     ensures_redundantly n == 0 ==> \result == 1;
    //@     ensures g_factorial_arr[0] == 1;
    //@     ensures \forall int k; 1 <= k <= n;
    //@                g_factorial_arr[k] == g_factorial_arr[k-1] * k;
    //@     ensures \result == g_factorial_arr[n];
    //@ also
    //@   public exceptional_behavior
    //@     requires n < 0;
    //@     signals_only IllegalArgumentException;  
    public static long factorial(int n) {
        if (n < 0) {
            throw new IllegalArgumentException("Input number cannot be negative");
        }
        //@ assert n >= 0;

        //@ set g_factorial_arr = new int[n+1];
        //@ set g_factorial_arr[0] = 1;
        long factorial = 1;
        //@ assert factorial == 1;
        
        //@ maintaining 1 <= i <= n + 1;
        //@ loop_writes factorial, g_factorial_arr[1..n];
        //@ maintaining \forall int k; 1 <= k < i;
        //@                g_factorial_arr[k] == g_factorial_arr[k-1] * k;
        //@ maintaining factorial == g_factorial_arr[i-1]; 
        //@ decreases n + 1 - i;
        for (int i = 1; i <= n; ++i) {
            factorial *= i;
            //@ set g_factorial_arr[i] = g_factorial_arr[i-1] * i;
        }

        //@ assert \forall int k; 1 <= k <= n; g_factorial_arr[k] == g_factorial_arr[k-1] * k;
        return factorial;
    }
}
