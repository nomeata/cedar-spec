@C("!")
forbid(
  principal is a in a::"DDjjj",
  action in [Action::"action"],
  resource == a::"DDjjj"
) when {
  (true && (a::"" has "Khhh")) && ((!a::"") has "")
};
