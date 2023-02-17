package org.lbee.twophase;

public class LogicalClock {

    private long start;
    private long syncVal;

    public LogicalClock() {
        start = System.currentTimeMillis();
    }

    public void sync(long clock) {
        //System.out.printf("sync clock: %s with %s.\n", this.getValue(), clock);
        long maxClock = Math.max(this.getValue(), clock) + 1;
        start -= maxClock - this.getValue();
    }

    public long getValue() {
        return System.currentTimeMillis() - this.start;
    }

    @Override
    public String toString() {
        return Long.toString(this.getValue());
    }
}
