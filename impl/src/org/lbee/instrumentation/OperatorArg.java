package org.lbee.instrumentation;

public record OperatorArg(String type) {

    @Override
    public String toString() {
        return "{\"type\":\"" + this.type + "\"}";
    }

}
