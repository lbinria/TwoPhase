package org.lbee.instrumentation;

public class FormalInstrumentationConfig {

    private final String producerName;
    private final boolean logicClock;

    public FormalInstrumentationConfig(String producerName, boolean logicClock) {
        this.producerName = producerName;
        this.logicClock = logicClock;
    }

    public boolean isLogicClock() {
        return logicClock;
    }
}
