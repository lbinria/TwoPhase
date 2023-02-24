package org.lbee.instrumentation;

import java.util.List;

public record Operator(String method, String targetOperator,
                       List<OperatorArgumentType> args) {

}
