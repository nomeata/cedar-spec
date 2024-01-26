forbid(
  principal is a,
  action == Action::"action",
  resource is a
) when {
  true && (a::"" in [a::"6666[\0\0\0\0\u{12}\0\0\06666\u{b}T\0\0\0Ӹ"])
};
