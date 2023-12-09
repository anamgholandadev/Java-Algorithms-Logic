package com.thealgorithms.devutils.nodes;

/**
 * Base class for any node implementation which contains a generic type
 * variable.
 *
 * All known subclasses: {@link TreeNode}, {@link SimpleNode}.
 *
 * @param <E> The type of the data held in the Node.
 *
 * @author <a href="https://github.com/aitorfi">aitorfi</a>
 */
public abstract class Node<E> {

    //@ spec_public 
    private /*@ nullable @*/ E data;

    //@ public normal_behavior
    //@ pure
    public Node() {
    }


    //@ ensures this.data == data;
    //@ pure
    public Node(/*@ nullable @*/ E data) {
        this.data = data;
    }

    //@ ensures \result == data;
    //@ pure
    public E getData() {
        return data;
    }

    //@ assigns this.data;
    //@ ensures this.data == data;
    public void setData(E data) {
        this.data = data;
    }
}
