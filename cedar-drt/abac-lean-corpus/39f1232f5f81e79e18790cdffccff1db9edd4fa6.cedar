permit(
  principal,
  action,
  resource is a in a::"\0\0\0\0\0\0\0\0\u{17}\u{17}\u{17}\0\0\0\0j"
) when {
  true && (((a::"\0\0\0\0\0\0\0\0\u{17}\u{17}\u{17}\0\0\0\0j" in a::"\0\0\0\0\0\0\0\0\u{17}\u{17}\u{17}\0\0\0\0j") == (false in principal)) == principal)
};
