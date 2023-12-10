package com.thealgorithms.devutils.entities;

public class ProcessDetails {

    //@ spec_public 
    private String processId;
    //@ spec_public 
    private int arrivalTime;
    //@ spec_public 
    private int burstTime;
    //@ spec_public 
    private int waitingTime;
    //@ spec_public 
    private int turnAroundTime;


    //@ ensures this.processId == processId;
    //@ ensures this.arrivalTime == arrivalTime;
    //@ ensures this.burstTime == burstTime;
    //@ pure
    public ProcessDetails(final String processId, final int arrivalTime, final int burstTime) {
        this.processId = processId;
        this.arrivalTime = arrivalTime;
        this.burstTime = burstTime;
    }

    //@ ensures \result == processId;
    //@ pure
    public String getProcessId() {
        return processId;
    }

    //@ ensures \result == arrivalTime;
    //@ pure
    public int getArrivalTime() {
        return arrivalTime;
    }

    
    //@ ensures \result == burstTime;
    //@ pure
    public int getBurstTime() {
        return burstTime;
    }

    //@ ensures \result == waitingTime;
    //@ pure
    public int getWaitingTime() {
        return waitingTime;
    }

    //@ ensures \result == turnAroundTime;
    //@ pure
    public int getTurnAroundTimeTime() {
        return turnAroundTime;
    }

    //@ assigns this.processId;
    //@ ensures this.processId == processId;
    public void setProcessId(final String processId) {
        this.processId = processId;
    }

    //@ assigns this.arrivalTime;
    //@ ensures this.arrivalTime == arrivalTime;
    public void setArrivalTime(final int arrivalTime) {
        this.arrivalTime = arrivalTime;
    }

    //@ assigns this.burstTime;
    //@ ensures this.burstTime == burstTime;
    public void setBurstTime(final int burstTime) {
        this.burstTime = burstTime;
    }

    //@ assigns this.waitingTime;
    //@ ensures this.waitingTime == waitingTime;
    public void setWaitingTime(final int waitingTime) {
        this.waitingTime = waitingTime;
    }

    //@ assigns this.turnAroundTime;
    //@ ensures this.turnAroundTime == turnAroundTime;
    public void setTurnAroundTimeTime(final int turnAroundTime) {
        this.turnAroundTime = turnAroundTime;
    }
}
