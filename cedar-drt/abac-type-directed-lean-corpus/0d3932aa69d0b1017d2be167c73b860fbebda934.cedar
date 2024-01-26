permit(
  principal in a::"\u{1}/6",
  action in [],
  resource is a in a::"\u{1}/6"
) when {
  (true && (action in a::"\u{1}/6")) && true
};
