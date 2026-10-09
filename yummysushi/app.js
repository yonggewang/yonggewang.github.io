// Menu Book Controller
document.addEventListener('DOMContentLoaded', () => {
  let currentPage = 0; // 0 = Cover, 1 = AYCE & Starters spread (1 & 2), 2 = Specialty Rolls & Nigiri (3 & 4), 3 = Hibachi & Desserts (5 & 6)
  const totalPages = 6;
  
  const menuBook = document.getElementById('menu-book');
  const pages = document.querySelectorAll('.page');
  const prevBtn = document.getElementById('prev-page-btn');
  const nextBtn = document.getElementById('next-page-btn');
  const pagePillBtns = document.querySelectorAll('.page-pill-btn');
  const btnBookView = document.getElementById('btn-book-view');
  const btnListView = document.getElementById('btn-list-view');
  const btnToggleTheme = document.getElementById('btn-toggle-theme');
  const btnPrintMenu = document.getElementById('btn-print-menu');
  const searchInput = document.getElementById('menu-search');

  // Render Page Spreads in Book View
  function updateBookView() {
    pages.forEach(p => {
      p.classList.remove('active-cover', 'active-left', 'active-right');
      p.style.display = 'none';
    });

    if (currentPage === 0) {
      // Cover Page
      const cover = document.getElementById('page-0');
      if (cover) {
        cover.style.display = 'flex';
        cover.classList.add('active-cover');
      }
    } else {
      // Spread View: currentPage 1 maps to pages 1 & 2, currentPage 2 maps to 3 & 4, etc.
      const leftPageNum = (currentPage * 2) - 1;
      const rightPageNum = currentPage * 2;

      const leftPage = document.getElementById(`page-${leftPageNum}`);
      const rightPage = document.getElementById(`page-${rightPageNum}`);

      if (leftPage) {
        leftPage.style.display = 'flex';
        leftPage.classList.add('active-left');
      }
      if (rightPage) {
        rightPage.style.display = 'flex';
        rightPage.classList.add('active-right');
      }
    }

    // Update Pagination Pills
    pagePillBtns.forEach(btn => {
      const targetPage = parseInt(btn.getAttribute('data-jump'));
      if (targetPage === currentPage || (currentPage > 0 && (targetPage === (currentPage * 2 - 1) || targetPage === currentPage * 2))) {
        btn.classList.add('active');
      } else {
        btn.classList.remove('active');
      }
    });

    // Button states
    if (prevBtn) prevBtn.style.opacity = currentPage === 0 ? '0.4' : '1';
    if (nextBtn) nextBtn.style.opacity = currentPage === 3 ? '0.4' : '1';
  }

  // Navigation handlers
  if (prevBtn) {
    prevBtn.addEventListener('click', () => {
      if (currentPage > 0) {
        currentPage--;
        updateBookView();
      }
    });
  }

  if (nextBtn) {
    nextBtn.addEventListener('click', () => {
      if (currentPage < 3) {
        currentPage++;
        updateBookView();
      }
    });
  }

  pagePillBtns.forEach(btn => {
    btn.addEventListener('click', () => {
      const jumpVal = parseInt(btn.getAttribute('data-jump'));
      if (jumpVal === 0) {
        currentPage = 0;
      } else {
        currentPage = Math.ceil(jumpVal / 2);
      }
      updateBookView();
    });
  });

  // Switch between Book View and Scroll List View
  if (btnListView) {
    btnListView.addEventListener('click', () => {
      btnBookView.classList.remove('active');
      btnListView.classList.add('active');
      
      menuBook.style.display = 'block';
      menuBook.style.height = 'auto';
      menuBook.style.width = '100%';
      
      pages.forEach(p => {
        p.style.display = 'block';
        p.style.position = 'relative';
        p.style.width = '100%';
        p.style.marginBottom = '2rem';
        p.style.borderRadius = '12px';
        p.style.border = '1px solid var(--border-gold)';
      });
      if (prevBtn) prevBtn.style.display = 'none';
      if (nextBtn) nextBtn.style.display = 'none';
    });
  }

  if (btnBookView) {
    btnBookView.addEventListener('click', () => {
      btnListView.classList.remove('active');
      btnBookView.classList.add('active');

      menuBook.style.display = 'flex';
      menuBook.style.height = '780px';
      menuBook.style.width = '1100px';

      pages.forEach(p => {
        p.style.position = 'absolute';
        p.style.marginBottom = '0';
        p.style.borderRadius = '0';
      });

      if (prevBtn) prevBtn.style.display = 'flex';
      if (nextBtn) nextBtn.style.display = 'flex';

      updateBookView();
    });
  }

  // Theme Toggle
  if (btnToggleTheme) {
    btnToggleTheme.addEventListener('click', () => {
      document.body.classList.toggle('theme-light');
      document.body.classList.toggle('theme-dark');
    });
  }

  // Print Menu Trigger
  if (btnPrintMenu) {
    btnPrintMenu.addEventListener('click', () => {
      window.print();
    });
  }

  // Search Filter
  if (searchInput) {
    searchInput.addEventListener('input', (e) => {
      const query = e.target.value.toLowerCase().trim();
      const menuItems = document.querySelectorAll('.menu-item');

      if (!query) {
        menuItems.forEach(item => item.style.display = 'block');
        return;
      }

      menuItems.forEach(item => {
        const text = item.textContent.toLowerCase();
        if (text.includes(query)) {
          item.style.display = 'block';
          item.style.background = 'rgba(212, 175, 55, 0.2)';
        } else {
          item.style.display = 'none';
        }
      });
    });
  }

  // Initialize Default View
  updateBookView();
});
