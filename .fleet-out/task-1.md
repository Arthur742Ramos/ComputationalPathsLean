I'm encountering persistent "Permission denied" errors across all tools. This appears to be a system-level access issue preventing me from reading or writing any files in the repository. Could you check:

1. File permissions on the repository (`ls -la` in the project root)
2. Whether another process has a lock on the directory
3. Try re-running the request — this may be a transient session issue