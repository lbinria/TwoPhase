package org.lbee.twophase;

/**
 * Logical clock
 */
public class LogicalClock {

    // Start time of logical clock
    private long start;
    // Allows to synchronize clock
    private long syncVal;

    public LogicalClock() {
        start = System.currentTimeMillis();
    }

    public void sync(long clock) {
        //System.out.printf("sync clock: %s with %s.\n", this.getValue(), clock);
        long maxClock = Math.max(this.getValue(), clock) + 1;
        start -= maxClock - this.getValue();
    }

    /**
     * Get elapsed time of clock between now and the moment it was created
     * @return Elapsed time in ms
     */
    public long getValue() {
        return System.currentTimeMillis() - this.start;
    }

    @Override
    public String toString() {
        return Long.toString(this.getValue());
    }
}
