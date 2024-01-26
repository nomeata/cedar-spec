permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (resource || (!(Fcch0ccc00000::"" <= principal)))) && principal
};
