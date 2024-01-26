permit(
  principal == Bsss::a::"6",
  action,
  resource
) when {
  false && (G::"6" in principal)
};
