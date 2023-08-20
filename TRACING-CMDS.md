How to get tracing logs during tests:

```powershell
$env:RUST_LOG = 'trace'; cargo nextest run NAME_OF_TEST --nocapture 1> trace.log
```