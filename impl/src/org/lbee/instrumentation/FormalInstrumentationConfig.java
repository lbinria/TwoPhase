package org.lbee.instrumentation;

import java.util.HashMap;
import java.util.Map;

public class FormalInstrumentationConfig {

    private final String producerName;
    private final boolean logicClock;
    private final Map<String, Map<String, Operator>> variables;

    public String getProducerName() {
        return producerName;
    }

    public FormalInstrumentationConfig(String producerName, boolean logicClock) {
        this.producerName = producerName;
        this.logicClock = logicClock;
        this.variables = new HashMap<>();
    }

    public void addVariable(String name, Map<String, Operator> operators) {
        variables.put(name, operators);
    }

    public boolean isLogicClock() {
        return logicClock;
    }


}
