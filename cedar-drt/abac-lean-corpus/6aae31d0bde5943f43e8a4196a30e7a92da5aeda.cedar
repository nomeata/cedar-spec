@r("\u{1}\0")
permit(
  principal,
  action,
  resource is a in a::""
) when {
  true && (context has "Ahh30")
};
