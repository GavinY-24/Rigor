#[test]
fn bootstrap_builds() {
    let k = rigor_certificates::bootstrap_kernel();
    match k {
        Ok(k) => { eprintln!("decls: {}", k.env.len()); }
        Err(e) => panic!("bootstrap failed: {e}"),
    }
}
