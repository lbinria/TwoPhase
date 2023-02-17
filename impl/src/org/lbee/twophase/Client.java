package org.lbee.twophase;

import java.io.*;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.UUID;

public class Client {

    public static void main(String[] args) {

        if (args.length < 3) {
            System.out.println("Missing arguments. hostname, port, type={tm, rm} expected.");
            return;
        }

        String hostname = args[0];
        int port = Integer.parseInt(args[1]);
        String type = args[2];

        final Configuration config = new Configuration(args);
        // Some printing
        System.out.println(config);

        try (Socket socket = new Socket(hostname, port)) {

            NetworkProcess2 manager;
            switch (type) {
                case "tm" :
                    manager = new TransactionManager2(socket, config.transactionManagerConfig);
                    break;
                case "rm" :
                    ResourceManager2 resourceManager = new ResourceManager2(socket, UUID.randomUUID().toString(), "TM", config.resourceManagerConfig);
                    resourceManager.register();
                    manager = resourceManager;
                    break;
                default : {
                    System.out.println("Expected type is tm or rm.");
                    return;
                }
            }

            do {
                manager.run();
            }
            while (!manager.isShutdown());

            // Send bye to server (kill the server thread)
            manager.sendRaw("bye");

            // Print end of process
            System.out.println("shutdown.");

        } catch (UnknownHostException ex) {

            System.out.println("Server not found: " + ex.getMessage());

        } catch (IOException ex) {

            System.out.println("I/O error: " + ex.getMessage());
        }
    }

    /* Stolen from lemmy */
    private static class Configuration {

        public int nResourceManager = 2;
        public TransactionManager2.TransactionManagerConfiguration transactionManagerConfig;
        public ResourceManager2.ResourceManagerConfiguration resourceManagerConfig;

        public Configuration(final String[] args) {
            this.transactionManagerConfig = new TransactionManager2.TransactionManagerConfiguration(nResourceManager, Integer.MAX_VALUE, false);
            this.resourceManagerConfig = new ResourceManager2.ResourceManagerConfiguration(false, -1, false);
        }

        @Override
        public String toString() {
            return "Configuration{" +
                    "transactionManagerConfig=" + transactionManagerConfig +
                    ", resourceManagerConfig=" + resourceManagerConfig +
                    '}';
        }
    }
}
