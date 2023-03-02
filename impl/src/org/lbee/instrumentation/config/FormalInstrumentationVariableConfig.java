package org.lbee.instrumentation.config;

import java.util.List;

public class FormalInstrumentationVariableConfig {

    private final String name;
    private final String mappedClass;
    private final List<Operator> operators;

    public FormalInstrumentationVariableConfig(String name, String mappedClass, List<Operator> operators) {
        this.name = name;
        this.mappedClass = mappedClass;
        this.operators = operators;
    }

}
