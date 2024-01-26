permit(
  principal,
  action,
  resource
) when {
  true && (g::B::A::"" in principal)
};
