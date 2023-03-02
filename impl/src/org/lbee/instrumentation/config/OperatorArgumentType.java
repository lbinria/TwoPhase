package org.lbee.instrumentation.config;

import java.util.ArrayList;
import java.util.List;

public final class OperatorArgumentType {

    private final String name;
    private final String type;
    private final List<OperatorArgumentType> args;

    public OperatorArgumentType(String name, String type) {
        this.name = name;
        this.type = type;
        this.args = new ArrayList<>();
    }

    public OperatorArgumentType(String type) {
        this.name = null;
        this.type = type;
        this.args = new ArrayList<>();
    }

    public OperatorArgumentType(String type, List<OperatorArgumentType> args) {
        this.name = null;
        this.type = type;
        this.args = args;
    }

    public String name() {
        return name;
    }

    public String type() {
        return type;
    }

}
