package org.lbee.instrumentation;

import java.util.List;
import java.util.stream.Collectors;

public record Operator(String method, String targetOperator,
                       List<OperatorArg> args) {

    @Override
    public String toString() {
        String strArgs = this.args.stream().map(OperatorArg::toString).collect(Collectors.joining(","));
        return "{\"target_operator\":\"" + this.targetOperator + "\", \"args\":[" + strArgs + "]}";
    }
}
