permit(
  principal,
  action,
  resource is a
) when {
  (true && (a::"" == ((a::"\u{2}\0" in principal) + principal))) && principal
};
