package org.lbee.protocol;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.util.Random;

public class Configuration {

    public TransactionManagerConfiguration tmConfig;
    public ResourceManagerConfiguration rmConfig;

    public Configuration(JsonObject jsonConfig) {
        JsonArray jsonResourceManagerNames = jsonConfig.get("RM").getAsJsonArray();
        this.tmConfig = new TransactionManagerConfiguration(jsonResourceManagerNames.size(), Integer.MAX_VALUE);
        this.rmConfig = new ResourceManagerConfiguration(false, -1);

    }

    @Override
    public String toString() {
        return "Configuration{" +
                "transactionManagerConfig=" + tmConfig +
                ", resourceManagerConfig=" + rmConfig +
                '}';
    }

}

/**
 * Configuration of a resource manager
 * @param shouldFail Is resource manager should fail, invoke an unknown exception
 * @param taskDuration Duration of the simulated task
 */
record ResourceManagerConfiguration(boolean shouldFail, int taskDuration) {

    ResourceManagerConfiguration(boolean shouldFail, int taskDuration) {
        this.shouldFail = shouldFail;

        if (taskDuration == -1)
            /* Set a random task duration */
            this.taskDuration = new Random().nextInt(500);
        else
            this.taskDuration = taskDuration;
    }

    @Override
    public String toString() {
        return "ResourceManagerConfiguration{" +
                "shouldFail=" + shouldFail +
                ", taskDuration=" + taskDuration +
                '}';
    }
}

/**
 * Configuration of a resource manager
 * @param timeout Is resource manager should fail, invoke an unknown exception
 */
record TransactionManagerConfiguration(int nResourceManager, int timeout) {
    @Override
    public String toString() {
        return "TransactionManagerConfiguration{" +
                "timeout=" + timeout +
                '}';
    }
}