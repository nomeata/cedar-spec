@r("\u{2}!")
forbid(
  principal is a in a::"DDjjj",
  action in [Action::"action"],
  resource == a::"DDjjj"
) when {
  (true && (a::"" has "Khhh")) && (({"Khhh": false} has "") has "")
};
