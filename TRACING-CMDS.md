How to get tracing logs during tests:

```powershell
# Run specific test:
$env:RUST_LOG = 'trace'; cargo nextest run NAME_OF_TEST --nocapture 1> trace.log

# Run all tests:
$env:RUST_LOG = 'trace'; cargo nextest run --nocapture 1> trace.log
```

```bash
# Run specific test:
RUST_LOG=trace cargo nextest run NAME_OF_TEST --nocapture 1> trace.log

# Run all tests:
RUST_LOG=trace cargo nextest run --nocapture 1> trace.log
```
